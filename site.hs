{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.List (intercalate, isPrefixOf, sort)
import Data.Maybe (fromMaybe)
import Hakyll
import System.Environment (lookupEnv)
import System.FilePath (dropExtension, splitDirectories, takeBaseName, takeFileName, (</>))
import Text.Pandoc.Options
  ( Extension (..)
  , Extensions
  , ReaderOptions (..)
  , disableExtension
  , enableExtension
  , githubMarkdownExtensions
  )

main :: IO ()
main = do
  baseUrl <- normalizeBaseUrl . fromMaybe "" <$> lookupEnv "PLFH_BASEURL"
  wasmRootfsUrl <- fromMaybe "" <$> lookupEnv "PLFH_WASM_ROOTFS_URL"
  hakyll $ do
    match "css/*" $ do
      route idRoute
      compile compressCssCompiler

    match "wasm/*" $ do
      route idRoute
      compile copyFileCompiler

    match "templates/*" $ compile templateBodyCompiler

    match "content/index.md" $ do
      route $ constRoute "index.html"
      compile $
        plfhPandocCompiler
          >>= loadAndApplyTemplate "templates/page.html" (pageCtx baseUrl wasmRootfsUrl)
          >>= loadAndApplyTemplate "templates/default.html" (pageCtx baseUrl wasmRootfsUrl)
          >>= applyBaseUrl baseUrl

    match (fromList
      [ "content/Overview.md"
      , "content/Playground.md"
      , "content/Preface.md"
      , "content/Setup.md"
      , "content/HaskLib.md"
      , "content/Status.md"
      , "content/Citing.md"
      ] .||. "content/part1/*.md" .||. "content/part2/*.md" .||. "content/part3/*.md") $ do
      route prettyPageRoute
      compile $
        plfhPandocCompiler
          >>= loadAndApplyTemplate "templates/page.html" (pageCtx baseUrl wasmRootfsUrl)
          >>= loadAndApplyTemplate "templates/default.html" (pageCtx baseUrl wasmRootfsUrl)
          >>= applyBaseUrl baseUrl

    -- Render all extracted Haskell chapters, client modules, negative controls,
    -- compiler reproducers, and HaskLib reference sources under /Source/.
    match sourcePatterns $ do
      route sourcePageRoute
      compile $ do
        ident <- getUnderlying
        let path = toFilePath ident
            ctx = sourceCtx path baseUrl wasmRootfsUrl
        haskellSourceCompiler
          >>= loadAndApplyTemplate "templates/source.html" ctx
          >>= loadAndApplyTemplate "templates/default.html" ctx
          >>= applyBaseUrl baseUrl

    -- Auto-generated /Source/ index page listing every rendered .hs module.
    create ["Source/index.html"] $ do
      route idRoute
      compile $ do
        chapterIds <- sort . map toFilePath <$> getMatches "hs/PLFH/**.hs"
        hasklibIds <- sort . map toFilePath <$> getMatches "reference/hasklib/**.hs"
        negIds <- sort . map toFilePath <$> getMatches "hs/negative/*.hs"
        openReproIds <- sort . map toFilePath <$> getMatches "reproducers/*.hs"
        fixedReproIds <- sort . map toFilePath <$> getMatches "reproducers/fixed/*.hs"
        let (chapMods, clientMods) = partitionChapterClients chapterIds
            md = buildSourceIndexMarkdown chapMods clientMods hasklibIds negIds openReproIds fixedReproIds
            ctx =
              constField "title" "Source Browser"
                <> constField "prevUrl" "/HaskLib/"
                <> constField "nextUrl" "/Status/"
                <> pageCtx baseUrl wasmRootfsUrl
        pandocItem <- readPandocWith plfhReaderOpts (Item (fromFilePath "source-index.md") md)
        makeItem (itemBody (writePandoc pandocItem))
          >>= loadAndApplyTemplate "templates/page.html" ctx
          >>= loadAndApplyTemplate "templates/default.html" ctx
          >>= applyBaseUrl baseUrl

sourcePatterns :: Pattern
sourcePatterns =
  "hs/PLFH/**.hs"
    .||. "hs/negative/*.hs"
    .||. "reproducers/*.hs"
    .||. "reproducers/fixed/*.hs"
    .||. "reference/hasklib/**.hs"

normalizeBaseUrl :: String -> String
normalizeBaseUrl "" = ""
normalizeBaseUrl s
  | last s == '/' = init s
  | otherwise     = s

-- | Map @content/Setup.md@ -> @Setup/index.html@ and
-- @content/part1/Naturals.md@ -> @Naturals/index.html@ (matching PLFA URLs).
prettyPageRoute :: Routes
prettyPageRoute = customRoute $ \ident ->
  let path = toFilePath ident
      base = takeBaseName (dropExtension path)
  in base </> "index.html"

-- | Map source file paths to clean URLs under @Source/@:
-- @hs/PLFH/Part1/Naturals.hs@ -> @Source/PLFH/Part1/Naturals/index.html@,
-- @reference/hasklib/HaskLib/Nat.hs@ -> @Source/hasklib/HaskLib/Nat/index.html@,
-- @reproducers/R13_Foo.hs@ -> @Source/reproducers/R13_Foo/index.html@.
sourcePageRoute :: Routes
sourcePageRoute = customRoute $ \ident ->
  sourceUrlSlug (toFilePath ident) </> "index.html"

sourceUrlSlug :: FilePath -> FilePath
sourceUrlSlug path =
  let stripped
        | "hs/" `isPrefixOf` path        = drop 3 path
        | "reference/" `isPrefixOf` path = drop 10 path
        | otherwise                      = path
  in "Source" </> dropExtension stripped

sourceHref :: FilePath -> String
sourceHref path = "/" ++ sourceUrlSlug path ++ "/"

plfhReaderOpts :: ReaderOptions
plfhReaderOpts = defaultHakyllReaderOptions
  { readerExtensions = plfhMarkdownExtensions
  }

-- | Compile Markdown with Pandoc + Skylighting, with TeX math disabled
-- (PLFH uses Unicode and clean HTML/CSS rather than heavy TeX/KaTeX).
plfhPandocCompiler :: Compiler (Item String)
plfhPandocCompiler =
  pandocCompilerWith plfhReaderOpts defaultHakyllWriterOptions

-- | Highlight a raw @.hs@ file using the same Pandoc + Skylighting pipeline.
haskellSourceCompiler :: Compiler (Item String)
haskellSourceCompiler = do
  item <- getResourceBody
  let fenced = "```haskell\n" ++ stripTrailingNewlines (itemBody item) ++ "\n```\n"
  pandocItem <- readPandocWith plfhReaderOpts (Item (fromFilePath "source.md") fenced)
  pure (item { itemBody = itemBody (writePandoc pandocItem) })
  where
    stripTrailingNewlines = reverse . dropWhile (`elem` ("\r\n" :: String)) . reverse

plfhMarkdownExtensions :: Extensions
plfhMarkdownExtensions =
  disableExtension Ext_tex_math_dollars
    . disableExtension Ext_tex_math_single_backslash
    . disableExtension Ext_tex_math_double_backslash
    . enableExtension Ext_fenced_code_attributes
    . enableExtension Ext_pipe_tables
    . enableExtension Ext_auto_identifiers
    . enableExtension Ext_header_attributes
    . enableExtension Ext_raw_html
    $ githubMarkdownExtensions

pageCtx :: String -> String -> Context String
pageCtx baseUrl wasmRootfsUrl =
  constField "baseurl" baseUrl
    <> (if null wasmRootfsUrl then mempty else constField "wasmRootfsUrl" wasmRootfsUrl)
    <> constField "siteTitle" "Programming Language Foundations in Haskell"
    <> constField "repoUrl" "https://github.com/Tritlo/PLFH"
    <> constField "repoBranch" "main"
    <> constField "plfaUrl" "https://plfa.inf.ed.ac.uk/"
    <> constField "licenseName" "Creative Commons Attribution 4.0 International License"
    <> constField "licenseUrl" "https://creativecommons.org/licenses/by/4.0/"
    <> field "prevUrl" (mkNavUrl "prev")
    <> field "nextUrl" (mkNavUrl "next")
    <> field "srcUrl" mkSrcUrl
    <> field "moduleSrcUrl" mkModuleSrcUrl
    <> field "wasmInteractive" mkWasmInteractive
    <> field "plfaEditionLabel" (mkDefaultMeta "plfaEdition" "PLFA")
    <> field "plfaAuthorsLabel" (mkDefaultMeta "plfaAuthors" "Philip Wadler, Wen Kokke, and Jeremy G. Siek")
    <> defaultContext

sourceCtx :: FilePath -> String -> String -> Context String
sourceCtx path baseUrl wasmRootfsUrl =
  constField "title" (sourceDisplayTitle path)
    <> constField "relPath" (sourceDisplayPath path)
    <> constField "githubUrl" (sourceGitHubUrl path)
    <> maybe mempty (constField "chapterUrl") (sourceChapterUrl path)
    <> (if "reference/hasklib/" `isPrefixOf` path
          then constField "hasklibRefUrl" "/HaskLib/"
          else mempty)
    <> pageCtx baseUrl wasmRootfsUrl

sourceDisplayTitle :: FilePath -> String
sourceDisplayTitle path
  | "hs/PLFH/" `isPrefixOf` path =
      intercalate "." (splitDirectories (dropExtension (drop 3 path)))
  | "reference/hasklib/" `isPrefixOf` path =
      intercalate "." (splitDirectories (dropExtension (drop 18 path)))
  | otherwise = takeFileName path

sourceDisplayPath :: FilePath -> String
sourceDisplayPath path
  | "reference/hasklib/" `isPrefixOf` path =
      let rel = drop 18 path
      in if "Prelude" `isPrefixOf` rel
           then "Tritlo/ghc: docs/dependent-haskell/examples/open-evaluation/" ++ rel
           else "Tritlo/ghc: docs/dependent-haskell/hasklib/" ++ rel
  | otherwise = path

sourceGitHubUrl :: FilePath -> String
sourceGitHubUrl path
  | "reference/hasklib/" `isPrefixOf` path =
      let rel = drop 18 path
      in if "Prelude" `isPrefixOf` rel
           then "https://github.com/Tritlo/ghc/blob/dependent-haskell/docs/dependent-haskell/examples/open-evaluation/" ++ rel
           else "https://github.com/Tritlo/ghc/blob/dependent-haskell/docs/dependent-haskell/hasklib/" ++ rel
  | otherwise = "https://github.com/Tritlo/PLFH/blob/main/" ++ path

-- | Standalone supporting client modules under hs/PLFH/ that are not chapters.
clientModuleNames :: [String]
clientModuleNames =
  [ "AnyWitnessIso"
  , "BigStepFunctional"
  , "BisimulationRenaming"
  , "InductionClient"
  , "ListsProof"
  , "RuntimeSmokeTest"
  ]

sourceChapterUrl :: FilePath -> Maybe String
sourceChapterUrl path
  | "hs/PLFH/Part" `isPrefixOf` path =
      let base = takeBaseName path
      in if base `elem` clientModuleNames
           then Nothing
           else Just ("/" ++ base ++ "/")
  | otherwise = Nothing

partitionChapterClients :: [FilePath] -> ([FilePath], [FilePath])
partitionChapterClients paths =
  ( [p | p <- paths, sourceChapterUrl p /= Nothing]
  , [p | p <- paths, sourceChapterUrl p == Nothing]
  )

buildSourceIndexMarkdown
  :: [FilePath] -> [FilePath] -> [FilePath] -> [FilePath] -> [FilePath] -> [FilePath] -> String
buildSourceIndexMarkdown chapMods clientMods hasklibIds negIds openReproIds fixedReproIds =
  unlines $
    [ "Browse every verified Haskell module extracted from PLFH, its supporting"
    , "client modules, the `HaskLib` reference library from `Tritlo/ghc`, all"
    , "negative controls, and every compiler reproducer directly on this site."
    , ""
    , "## Chapter Modules (" ++ show (length chapMods) ++ ")"
    , ""
    ]
      ++ map formatChapterRow chapMods
      ++ [ ""
         , "## Supporting Client Modules & Smoke Tests (" ++ show (length clientMods) ++ ")"
         , ""
         ]
      ++ map formatPlainRow clientMods
      ++ [ ""
         , "## `HaskLib` Reference Modules (" ++ show (length hasklibIds) ++ ")"
         , ""
         , "See the [HaskLib Reference](/HaskLib/) page for the exported API summary."
         , ""
         ]
      ++ map formatPlainRow hasklibIds
      ++ [ ""
         , "## Negative Controls (" ++ show (length negIds) ++ ")"
         , ""
         ]
      ++ map formatPlainRow negIds
      ++ [ ""
         , "## Open Compiler-Gap Reproducers (" ++ show (length openReproIds) ++ ")"
         , ""
         ]
      ++ map formatPlainRow openReproIds
      ++ [ ""
         , "## Fixed Regressions (" ++ show (length fixedReproIds) ++ ")"
         , ""
         ]
      ++ map formatPlainRow fixedReproIds
  where
    formatChapterRow p =
      let modName = sourceDisplayTitle p
          chapLink = case sourceChapterUrl p of
            Just u  -> " ([chapter](" ++ u ++ "))"
            Nothing -> ""
      in "- [`" ++ modName ++ "`](" ++ sourceHref p ++ ")" ++ chapLink

    formatPlainRow p =
      "- [`" ++ sourceDisplayTitle p ++ "`](" ++ sourceHref p ++ ")"

mkDefaultMeta :: String -> String -> Item a -> Compiler String
mkDefaultMeta key fallback item = do
  mVal <- getMetadataField (itemIdentifier item) key
  pure (fromMaybe fallback mVal)

mkNavUrl :: String -> Item a -> Compiler String
mkNavUrl key item = do
  mVal <- getMetadataField (itemIdentifier item) key
  case mVal of
    Nothing -> noResult ("No metadata field: " ++ key)
    Just path -> pure path

mkSrcUrl :: Item a -> Compiler String
mkSrcUrl item = do
  mVal <- getMetadataField (itemIdentifier item) "src"
  case mVal of
    Nothing -> noResult "No metadata field: src"
    Just rel -> pure ("https://github.com/Tritlo/PLFH/blob/main/" ++ rel)

mkModuleSrcUrl :: Item a -> Compiler String
mkModuleSrcUrl item = do
  mVal <- getMetadataField (itemIdentifier item) "module"
  case mVal of
    Nothing -> noResult "No metadata field: module"
    Just modName ->
      let slug = map (\c -> if c == '.' then '/' else c) modName
      in pure ("/Source/" ++ slug ++ "/")

mkWasmInteractive :: Item a -> Compiler String
mkWasmInteractive item = do
  mMod <- getMetadataField (itemIdentifier item) "module"
  mPlay <- getMetadataField (itemIdentifier item) "playground"
  case (mMod, mPlay) of
    (Just _, _) -> pure "true"
    (_, Just _) -> pure "true"
    _           -> noResult "Not an interactive Wasm page"

-- | Prefix root-relative links with @PLFH_BASEURL@ for GitHub Pages project sites
-- (e.g. @/PLFH@), or relativize URLs when building for local preview.
applyBaseUrl :: String -> Item String -> Compiler (Item String)
applyBaseUrl "" item = relativizeUrls item
applyBaseUrl baseUrl item =
  pure $ fmap (withUrls prefixRoot) item
  where
    prefixRoot url
      | "//" `isPrefixOf` url      = url
      | baseUrl `isPrefixOf` url   = url
      | "/" `isPrefixOf` url       = baseUrl ++ url
      | otherwise                  = url
