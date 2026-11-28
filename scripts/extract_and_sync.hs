#!/usr/bin/env -S runhaskell --ghc-arg=-package-env=-
{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE CPP #-}

{- |
Module      : Main
Description : Extract checked Haskell modules and negative controls from PLFH Markdown chapters

Extracts executable @.hs@ modules and negative controls from the literate
Markdown chapters under @content/@ into @hs/@. Optionally mirrors @hs/@ into a
GHC fork directory and snapshots @dependent-base@ sources into
@reference/dependent-base/@.
-}
module Main (main) where

import Control.Monad (forM_, when)
import Data.Char (isAlphaNum, isSpace)
import Data.List (intercalate, isPrefixOf, sort)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import System.Directory (
    canonicalizePath,
    copyFileWithMetadata,
    createDirectoryIfMissing,
    doesDirectoryExist,
    doesFileExist,
    getCurrentDirectory,
    listDirectory,
    removePathForcibly,
 )
import System.Environment (getArgs, getProgName)
import System.Exit (ExitCode (..), exitSuccess, exitWith)
import System.FilePath (
    makeRelative,
    splitDirectories,
    takeDirectory,
    takeFileName,
    (<.>),
    (</>),
 )
import System.IO (hPutStrLn, stderr)

-- | Parsed CLI options for @extract_and_sync.hs@.
data Options = Options
    { optSyncGhc :: Maybe FilePath
    , optSyncDependentBase :: Maybe FilePath
    }
    deriving (Eq, Show)

-- | Negative control extracted from a @.fail@ fenced Haskell block.
data NegativeControl = NegativeControl
    { ncName :: String
    , ncExpect :: String
    , ncCode :: String
    }
    deriving (Eq, Show)

-- | Parsed metadata for a fenced code block opening line.
data FenceInfo = FenceInfo
    { fiLang :: String
    , fiClasses :: Set.Set String
    , fiAttrs :: Map.Map String String
    }
    deriving (Eq, Show)

-- | State machine while scanning a Markdown chapter line by line.
data ScanState = ScanState
    { ssInFence :: Bool
    , ssFence :: FenceInfo
    , ssFenceStart :: Int
    , ssBuf :: [String]
    , ssModuleChunks :: [(Int, [String])]
    , ssNegControls :: [NegativeControl]
    }

-- | Trim leading and trailing whitespace.
trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

-- | Strip matching single or double quotes from both ends.
stripQuotes :: String -> String
stripQuotes = stripChar '\'' . stripChar '"'
  where
    stripChar q s = reverse (dropWhile (== q) (reverse (dropWhile (== q) s)))

-- | Split a string on a single delimiter character.
splitOn :: Char -> String -> [String]
splitOn sep = go
  where
    go [] = [""]
    go xs =
        case break (== sep) xs of
            (chunk, []) -> [chunk]
            (chunk, _ : rest) -> chunk : go rest

-- | Join path components with forward slashes.
toPosixRel :: FilePath -> FilePath -> String
toPosixRel base target = intercalate "/" (splitDirectories (makeRelative base target))

-- | Parse simple @key: value@ YAML frontmatter delimited by @---@ lines.
parseFrontmatter :: [String] -> Map.Map String String
parseFrontmatter ("---" : rest) =
    case break (== "---") rest of
        (fmLines, "---" : _) ->
            Map.fromList (catMaybes (map parseLine fmLines))
        _ -> Map.empty
  where
    parseLine line =
        case break (== ':') line of
            (k, ':' : v) -> Just (trim k, stripQuotes (trim v))
            _ -> Nothing
parseFrontmatter _ = Map.empty

-- | Tokenize a Pandoc brace attribute block such as @.haskell .fail name="Foo" expect="GHC-83865"@.
tokenizeBraceAttrs :: String -> [String]
tokenizeBraceAttrs = go . dropWhile isSpace
  where
    go [] = []
    go s =
        let (tok, rest) = takeToken s
         in tok : go (dropWhile isSpace rest)

    takeToken s
        | Just (key, '=' : '"' : afterQ) <- splitKeyEq s =
            let (val, rest0) = break (== '"') afterQ
                (quoted, rest1) = case rest0 of
                    '"' : r -> (key ++ "=\"" ++ val ++ "\"", r)
                    _ -> (key ++ "=\"" ++ val, [])
             in (quoted, rest1)
        | otherwise = break isSpace s

    splitKeyEq str =
        let (k, r) = span (\c -> isAlphaNum c || c == '_' || c == '-') str
         in if not (null k) && "=" `isPrefixOf` r
                then Just (k, r)
                else Nothing

-- | Parse a fenced code block info string (@haskell@ or @{.haskell .wip name="Foo"}@).
parseFenceInfo :: String -> FenceInfo
parseFenceInfo raw =
    let info = trim raw
     in if null info
            then emptyFence
            else
                if "{" `isPrefixOf` info && "}" `isSuffixOfStr` info
                    then parseBrace (trim (take (length info - 2) (drop 1 info)))
                    else parsePlain (words info)
  where
    emptyFence = FenceInfo "" Set.empty Map.empty
    knownLangs = ["haskell", "bash", "sh", "nix", "text"]

    parseBrace inner =
        foldl step emptyFence (tokenizeBraceAttrs inner)
      where
        step fi tok
            | '.' : cls <- tok =
                if null (fiLang fi) && cls `elem` knownLangs
                    then fi{fiLang = cls}
                    else fi{fiClasses = Set.insert cls (fiClasses fi)}
            | (k, '=' : v) <- break (== '=') tok =
                fi{fiAttrs = Map.insert k (stripQuotes v) (fiAttrs fi)}
            | otherwise = fi

    parsePlain [] = emptyFence
    parsePlain (lang : rest) =
        foldl step (FenceInfo lang Set.empty Map.empty) rest
      where
        step fi tok
            | (k, '=' : v) <- break (== '=') tok =
                fi{fiAttrs = Map.insert k (stripQuotes v) (fiAttrs fi)}
            | otherwise =
                fi{fiClasses = Set.insert tok (fiClasses fi)}

    isSuffixOfStr suf s = drop (length s - length suf) s == suf

-- | Extract checked module code and negative controls from one Markdown chapter.
extractChapter :: FilePath -> FilePath -> FilePath -> IO (Maybe FilePath, [NegativeControl])
extractChapter root hsDir mdPath = do
    text <- readFile mdPath
    let ls = lines text
        meta = parseFrontmatter ls
        mbModName = Map.lookup "module" meta
        relMd = toPosixRel root mdPath
        initState =
            ScanState
                { ssInFence = False
                , ssFence = FenceInfo "" Set.empty Map.empty
                , ssFenceStart = 0
                , ssBuf = []
                , ssModuleChunks = []
                , ssNegControls = []
                }
        finalState = foldl step initState (zip [1 :: Int ..] ls)
        chunks = reverse (ssModuleChunks finalState)
        negs = reverse (ssNegControls finalState)

    mbOut <-
        case (mbModName, chunks) of
            (Just modName, firstChunk : restChunks) -> do
                let modParts = splitOn '.' modName
                    outPath = foldl (</>) hsDir modParts <.> "hs"
                createDirectoryIfMissing True (takeDirectory outPath)
                let outLines = renderExtractedModule relMd firstChunk restChunks
                writeFile outPath (intercalate "\n" outLines)
                pure (Just outPath)
            _ -> pure Nothing

    pure (mbOut, negs)
  where
    skipClasses = Set.fromList ["wip", "exercise", "ignore", "spec"]

    step st (idx, line)
        | not (ssInFence st) =
            case stripPrefixMaybe "```" line of
                Just afterTicks
                    | not (null (trim afterTicks)) ->
                        st
                            { ssInFence = True
                            , ssFence = parseFenceInfo afterTicks
                            , ssFenceStart = idx + 1
                            , ssBuf = []
                            }
                _
                    | trim line == "```" ->
                        st
                            { ssInFence = True
                            , ssFence = FenceInfo "" Set.empty Map.empty
                            , ssFenceStart = idx + 1
                            , ssBuf = []
                            }
                    | otherwise -> st
        | trim line == "```" =
            let fi = ssFence st
                chunkLines = reverse (ssBuf st)
                stClosed = st{ssInFence = False, ssBuf = []}
             in if fiLang fi /= "haskell"
                    then stClosed
                    else
                        if "fail" `Set.member` fiClasses fi
                            then case Map.lookup "name" (fiAttrs fi) of
                                Just name
                                    | not (null name) ->
                                        let expect = Map.findWithDefault "" "expect" (fiAttrs fi)
                                            code = intercalate "\n" chunkLines ++ "\n"
                                            nc = NegativeControl name expect code
                                         in stClosed{ssNegControls = nc : ssNegControls stClosed}
                                _ -> stClosed
                            else
                                if Set.null (Set.intersection (fiClasses fi) skipClasses)
                                    then stClosed{ssModuleChunks = (ssFenceStart st, chunkLines) : ssModuleChunks stClosed}
                                    else stClosed
        | otherwise = st{ssBuf = line : ssBuf st}

    stripPrefixMaybe pref xs
        | pref `isPrefixOf` xs = Just (drop (length pref) xs)
        | otherwise = Nothing

-- | Render extracted module chunks with @{-# LINE ... #-}@ pragmas preserving leading pragmas.
renderExtractedModule :: String -> (Int, [String]) -> [(Int, [String])] -> [String]
renderExtractedModule relMd (firstLine, firstChunk) restChunks =
    header ++ firstBody ++ concatMap renderExtra restChunks
  where
    header =
        [ "-- Generated from " ++ relMd ++ " by scripts/extract_and_sync.hs"
        , "-- Do not edit directly; edit the literate Markdown chapter instead."
        , ""
        ]

    isLeadingPragma line = "{-#" `isPrefixOf` line || null (trim line)
    (pragmas, afterPragmas) = span isLeadingPragma firstChunk

    firstBody
        | not (null pragmas) =
            pragmas
                ++ if null afterPragmas
                    then []
                    else [linePragma (firstLine + length pragmas)] ++ afterPragmas ++ [""]
        | otherwise =
            [linePragma firstLine] ++ firstChunk ++ [""]

    renderExtra (startLine, chunk) =
        [linePragma startLine] ++ chunk ++ [""]

    linePragma n = "{-# LINE " ++ show n ++ " \"" ++ relMd ++ "\" #-}"

-- | Write extracted negative control modules into @hs/negative/@.
writeNegativeControls :: FilePath -> [NegativeControl] -> IO [FilePath]
writeNegativeControls _ [] = pure []
writeNegativeControls negDir negs = do
    createDirectoryIfMissing True negDir
    mapM writeOne negs
  where
    writeOne nc = do
        let path = negDir </> (ncName nc <.> "hs")
            codeLines = lines (ncCode nc)
            (pragmas, rest) = span ("{-#" `isPrefixOf`) codeLines
            expectLine = ["-- EXPECT-ERROR: " ++ ncExpect nc | not (null (ncExpect nc))]
            finalText = intercalate "\n" (pragmas ++ expectLine ++ rest) ++ "\n"
        writeFile path finalText
        pure path

-- | Recursively collect files matching a predicate in sorted path order.
findFiles :: (FilePath -> Bool) -> FilePath -> IO [FilePath]
findFiles predFile dir = do
    entries <- sort <$> listDirectory dir
    concat <$> mapM visit entries
  where
    visit entry = do
        let path = dir </> entry
        isDir <- doesDirectoryExist path
        if isDir
            then findFiles predFile path
            else pure [path | predFile path]

-- | Recursively copy a directory tree preserving file metadata.
copyTree :: FilePath -> FilePath -> IO ()
copyTree src dst = do
    createDirectoryIfMissing True dst
    entries <- sort <$> listDirectory src
    forM_ entries $ \entry -> do
        let s = src </> entry
            d = dst </> entry
        isDir <- doesDirectoryExist s
        if isDir
            then copyTree s d
            else copyFileWithMetadata s d

-- | Mirror @hs/@ into a GHC fork's @docs/dependent-haskell/plfh/@ directory.
syncToGhc :: FilePath -> FilePath -> IO ()
syncToGhc hsDir ghcPlfhDir = do
    createDirectoryIfMissing True ghcPlfhDir
    let dst = ghcPlfhDir </> "hs"
    removePathForcibly dst
    hasSrc <- doesDirectoryExist hsDir
    when hasSrc (copyTree hsDir dst)
    putStrLn ("Synced hs/ -> " ++ ghcPlfhDir)

-- | Snapshot @.hs@ files from @dependent-base/src@ into @reference/dependent-base/@.
syncDependentBaseReference :: FilePath -> FilePath -> FilePath -> IO ()
syncDependentBaseReference root depBaseRefDir depBaseSrcDir = do
    isDir <- doesDirectoryExist depBaseSrcDir
    when (not isDir) $ do
        hPutStrLn stderr ("ERROR: dependent-base src dir not found: " ++ depBaseSrcDir)
        exitWith (ExitFailure 1)
    removePathForcibly depBaseRefDir
    hsFiles <- findFiles (isSuffixOfStr ".hs") depBaseSrcDir
    forM_ hsFiles $ \src -> do
        let rel = makeRelative depBaseSrcDir src
            dst = depBaseRefDir </> rel
        createDirectoryIfMissing True (takeDirectory dst)
        copyFileWithMetadata src dst
    putStrLn
        ( "Synced "
            ++ show (length hsFiles)
            ++ " dependent-base reference file(s) -> "
            ++ toPosixRel root depBaseRefDir
        )
  where
    isSuffixOfStr suf s = drop (length s - length suf) s == suf

-- | Resolve the PLFH repository root from the script location or working directory.
resolveRepoRoot :: IO FilePath
resolveRepoRoot = do
    let scriptFile = __FILE__
    scriptExists <- doesFileExist scriptFile
    if scriptExists
        then do
            absScript <- canonicalizePath scriptFile
            let scriptDir = takeDirectory absScript
            if takeFileName scriptDir == "scripts"
                then pure (takeDirectory scriptDir)
                else findFromCwd
        else findFromCwd
  where
    findFromCwd = do
        cwd <- getCurrentDirectory
        hasContent <- doesDirectoryExist (cwd </> "content")
        if hasContent
            then pure cwd
            else do
                let parent = takeDirectory cwd
                parentHasContent <- doesDirectoryExist (parent </> "content")
                if parentHasContent then pure parent else pure cwd

-- | Parse command-line arguments.
parseArgs :: [String] -> Either String (Maybe Options)
parseArgs = go (Options Nothing Nothing)
  where
    go opts [] = Right (Just opts)
    go _ ("-h" : _) = Right Nothing
    go _ ("--help" : _) = Right Nothing
    go opts ("--sync-ghc" : dir : rest) = go opts{optSyncGhc = Just dir} rest
    go opts (arg : rest)
        | Just dir <- stripPrefixMaybe "--sync-ghc=" arg = go opts{optSyncGhc = Just dir} rest
    go opts ("--sync-dependent-base" : dir : rest) = go opts{optSyncDependentBase = Just dir} rest
    go opts (arg : rest)
        | Just dir <- stripPrefixMaybe "--sync-dependent-base=" arg = go opts{optSyncDependentBase = Just dir} rest
    go _ (bad : _) = Left ("unrecognized argument: " ++ bad)

    stripPrefixMaybe pref xs
        | pref `isPrefixOf` xs = Just (drop (length pref) xs)
        | otherwise = Nothing

-- | Print CLI usage summary.
printUsage :: String -> IO ()
printUsage prog = do
    putStrLn ("usage: " ++ prog ++ " [--sync-ghc PATH] [--sync-dependent-base PATH]")
    putStrLn ""
    putStrLn "Extract checked Haskell modules and negative controls from PLFH Markdown chapters."
    putStrLn "  --sync-ghc PATH             Mirror hs/ into GHC docs/dependent-haskell/plfh"
    putStrLn "  --sync-dependent-base PATH  Snapshot dependent-base src/ into reference/dependent-base/"

-- | Entry point.
main :: IO ()
main = do
    prog <- getProgName
    rawArgs <- getArgs
    opts <- case parseArgs rawArgs of
        Left err -> do
            hPutStrLn stderr ("ERROR: " ++ err)
            printUsage prog
            exitWith (ExitFailure 2)
        Right Nothing -> do
            printUsage prog
            exitSuccess
        Right (Just o) -> pure o

    root <- resolveRepoRoot
    let contentDir = root </> "content"
        clientsDir = root </> "clients"
        hsDir = root </> "hs"
        negDir = hsDir </> "negative"
        depBaseRefDir = root </> "reference" </> "dependent-base"

    removePathForcibly hsDir
    hasClients <- doesDirectoryExist clientsDir
    when hasClients (copyTree clientsDir hsDir)

    mdFiles <- findFiles (\p -> drop (length p - 3) p == ".md") contentDir
    extracted <- mapM (extractChapter root hsDir) mdFiles
    let modPaths = catMaybes (map fst extracted)
        allNegs = concatMap snd extracted

    negPaths <- writeNegativeControls negDir allNegs
    putStrLn
        ( "Extracted "
            ++ show (length modPaths)
            ++ " module(s) and "
            ++ show (length negPaths)
            ++ " negative control(s)."
        )
    forM_ modPaths $ \p -> putStrLn ("  module: " ++ toPosixRel root p)
    forM_ negPaths $ \p -> putStrLn ("  neg:    " ++ toPosixRel root p)

    forM_ (optSyncGhc opts) (syncToGhc hsDir)
    forM_ (optSyncDependentBase opts) (syncDependentBaseReference root depBaseRefDir)
