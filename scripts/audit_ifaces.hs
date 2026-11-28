#!/usr/bin/env -S runhaskell --ghc-arg=-package-env=-
{-# LANGUAGE GHC2024 #-}

{- |
Module      : Main
Description : Audit compiled PLFH .hi interfaces for silent function-kinded type variables

Inspects every compiled @.hi@ interface under @<build-dir>/PLFH@ with
@ghc --show-iface@ and rejects unexpected function-kinded type variables bound
under @forall@ (for example, an unqualified function name silently quantified as
a fresh type variable in a GADT constructor).
-}
module Main (main) where

import Data.Char (isAlphaNum, isAsciiLower, isSpace)
import Data.List (isInfixOf, isPrefixOf, sort)
import Data.Set qualified as Set
import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (getArgs, getProgName)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath (makeRelative, splitDirectories, (</>))
import System.IO (hPutStrLn, stderr)
import System.Process (readProcessWithExitCode)

{- | Explicit allowlist of intentional higher-order type parameters
(predicates, binary relations, type constructors, and reduction relations).
-}
allowedHoTyVars :: Set.Set String
allowedHoTyVars =
    Set.fromList
        [ "a"
        , "b"
        , "c"
        , "d"
        , "e"
        , "f"
        , "g"
        , "h"
        , "k"
        , "m"
        , "n"
        , "p"
        , "q"
        , "r"
        , "rel"
        , "step"
        ]

-- | Check whether a character belongs to a word token for boundary matching.
isWordChar :: Char -> Bool
isWordChar c = isAlphaNum c || c == '_'

-- | Collapse GHC interface continuation lines (@\n@ followed by indentation).
collapseContinuations :: String -> String
collapseContinuations [] = []
collapseContinuations ('\n' : rest) =
    case span (\c -> isSpace c && c /= '\n') rest of
        ([], _) -> '\n' : collapseContinuations rest
        (_, afterWs) -> ' ' : collapseContinuations afterWs
collapseContinuations (c : cs) = c : collapseContinuations cs

{- | Extract every @forall ... .@ binder header from normalized interface text.
Module-qualified names contain @.@ inside kinds (for example
@PLFH.Part2.Untyped.UTerm@), so the header ends at a @.@ followed by whitespace
or end of input.
-}
extractForallHeaders :: String -> [String]
extractForallHeaders = go Nothing
  where
    go :: Maybe Char -> String -> [String]
    go _ [] = []
    go prev s@(c : cs)
        | not (maybe False isWordChar prev)
        , Just afterForall <- stripForallWord s =
            case splitToForallDot afterForall of
                Just (hdr, rest) -> hdr : go (Just '.') rest
                Nothing -> []
        | otherwise = go (Just c) cs

    stripForallWord :: String -> Maybe String
    stripForallWord txt =
        case stripPrefixMaybe "forall" txt of
            Just rest@(next : _) | not (isWordChar next) -> Just rest
            Just [] -> Just []
            _ -> Nothing

    stripPrefixMaybe :: String -> String -> Maybe String
    stripPrefixMaybe pref xs
        | pref `isPrefixOf` xs = Just (drop (length pref) xs)
        | otherwise = Nothing

    splitToForallDot :: String -> Maybe (String, String)
    splitToForallDot = scan []
      where
        scan _ [] = Nothing
        scan acc ('.' : []) = Just (reverse acc, [])
        scan acc ('.' : r@(n : _))
            | isSpace n = Just (reverse acc, r)
        scan acc (x : xs) = scan (x : acc) xs

{- | Extract top-level @(name :: kind)@ and @{name :: kind}@ binders with
arbitrary nested parentheses or braces inside @kind@.
-}
extractBalancedBinders :: String -> [(String, String)]
extractBalancedBinders [] = []
extractBalancedBinders (c : cs)
    | c == '(' || c == '{' =
        let closeCh = if c == '(' then ')' else '}'
         in case takeBalanced c closeCh 1 [] cs of
                Just (inner, rest) ->
                    case parseBinderHead inner of
                        Just binder -> binder : extractBalancedBinders rest
                        Nothing -> extractBalancedBinders rest
                Nothing -> extractBalancedBinders cs
    | otherwise = extractBalancedBinders cs
  where
    takeBalanced :: Char -> Char -> Int -> String -> String -> Maybe (String, String)
    takeBalanced _ _ 0 acc rest = Just (reverse acc, rest)
    takeBalanced _ _ _ _ [] = Nothing
    takeBalanced openCh closeCh depth acc (x : xs)
        | x == openCh = takeBalanced openCh closeCh (depth + 1) (x : acc) xs
        | x == closeCh =
            if depth == 1
                then Just (reverse acc, xs)
                else takeBalanced openCh closeCh (depth - 1) (x : acc) xs
        | otherwise = takeBalanced openCh closeCh depth (x : acc) xs

-- | Parse @name :: kind@ from the trimmed body of a binder group.
parseBinderHead :: String -> Maybe (String, String)
parseBinderHead raw =
    case dropWhile isSpace raw of
        (c : rest)
            | isAsciiLower c ->
                let (tailChars, afterName) = span isIdentChar rest
                    name = c : tailChars
                 in case dropWhile isSpace afterName of
                        ':' : ':' : kindRaw -> Just (name, trim kindRaw)
                        _ -> Nothing
        _ -> Nothing
  where
    isIdentChar ch = isAlphaNum ch || ch == '_' || ch == '\''

-- | Trim leading and trailing whitespace.
trim :: String -> String
trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse

-- | Recursively collect all @.hi@ files under a directory in sorted order.
findHiFiles :: FilePath -> IO [FilePath]
findHiFiles dir = do
    entries <- sort <$> listDirectory dir
    concat <$> mapM visit entries
  where
    visit entry = do
        let path = dir </> entry
        isDir <- doesDirectoryExist path
        if isDir
            then findHiFiles path
            else pure [path | ".hi" `isSuffixOfStr` entry]

    isSuffixOfStr suf s = drop (length s - length suf) s == suf

-- | Convert a file path to forward-slash POSIX notation for diagnostics.
toPosixRel :: FilePath -> FilePath -> String
toPosixRel base target = joinSlash (splitDirectories (makeRelative base target))
  where
    joinSlash [] = ""
    joinSlash [x] = x
    joinSlash (x : xs) = x ++ "/" ++ joinSlash xs

-- | Audit one compiled @.hi@ file and return findings plus seen allowed params.
auditOneIface ::
    FilePath ->
    FilePath ->
    FilePath ->
    IO ([(String, String, String)], Set.Set String)
auditOneIface ghc buildDir hiPath = do
    let rel = toPosixRel buildDir hiPath
    (code, stdoutTxt, stderrTxt) <- readProcessWithExitCode ghc ["--show-iface", hiPath] ""
    case code of
        ExitFailure n -> do
            hPutStrLn stderr ("ERROR: " ++ ghc ++ " --show-iface " ++ hiPath ++ " exited " ++ show n)
            hPutStrLn stderr stderrTxt
            exitWith (ExitFailure n)
        ExitSuccess -> do
            let normalized = collapseContinuations stdoutTxt
                binders = concatMap extractBalancedBinders (extractForallHeaders normalized)
                step (finds, allowed) (name, kind)
                    | "->" `isInfixOf` kind =
                        if name `Set.member` allowedHoTyVars
                            then (finds, Set.insert name allowed)
                            else ((rel, name, kind) : finds, allowed)
                    | otherwise = (finds, allowed)
                (revFinds, seenAllowed) = foldl step ([], Set.empty) binders
            pure (reverse revFinds, seenAllowed)

-- | Entry point: @audit_ifaces.hs <ghc> <build-dir>@.
main :: IO ()
main = do
    args <- getArgs
    prog <- getProgName
    case args of
        [ghc, buildDir] -> do
            let plfhDir = buildDir </> "PLFH"
            exists <- doesDirectoryExist plfhDir
            if not exists
                then do
                    hPutStrLn stderr ("ERROR: " ++ plfhDir ++ " not found")
                    exitWith (ExitFailure 2)
                else do
                    his <- findHiFiles plfhDir
                    results <- mapM (auditOneIface ghc buildDir) his
                    let findings = concatMap fst results
                        seenAllowed = Set.unions (map snd results)
                    if not (null findings)
                        then do
                            putStrLn "  [FAIL] Interface soundness audit detected suspicious function-kinded type variables:"
                            mapM_
                                (\(rel, name, kind) -> putStrLn ("    - " ++ rel ++ ": (" ++ name ++ " :: " ++ kind ++ ")"))
                                findings
                            exitWith (ExitFailure 1)
                        else do
                            putStrLn
                                ( "  [PASS] Interface soundness audit: "
                                    ++ show (length his)
                                    ++ " .hi files clean (0 unintended function tyvars; allowed HO params seen: "
                                    ++ show (Set.toAscList seenAllowed)
                                    ++ ")"
                                )
        _ -> do
            hPutStrLn stderr ("usage: " ++ prog ++ " <ghc> <build-dir>")
            exitWith (ExitFailure 2)
