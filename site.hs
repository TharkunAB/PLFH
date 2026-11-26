{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.List (intercalate, isPrefixOf, isSuffixOf, sort)
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

siteOrigin :: String
siteOrigin = "https://plfh.tharkun.se"

defaultDescription :: String
defaultDescription =
  "Dependent Haskell in GHC 10.1 (-XDependentTypes): routes as values, runtime monad stacks, type-level case and lambdas, and a 25-chapter textbook running live in WebAssembly."

main :: IO ()
main = do
  baseUrl <- normalizeBaseUrl . fromMaybe "" <$> lookupEnv "PLFH_BASEURL"
  wasmRootfsUrl <- fromMaybe "" <$> lookupEnv "PLFH_WASM_ROOTFS_URL"
  hakyll $ do
    match "css/*" $ do
      route idRoute
      compile compressCssCompiler

    match "images/*" $ do
      route idRoute
      compile copyFileCompiler

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
      , "content/DependentBase.md"
      , "content/Status.md"
      , "content/Citing.md"
      ] .||. "content/part1/*.md" .||. "content/part2/*.md" .||. "content/part3/*.md") $ do
      route prettyPageRoute
      compile $
        plfhPandocCompiler
          >>= loadAndApplyTemplate "templates/page.html" (pageCtx baseUrl wasmRootfsUrl)
          >>= loadAndApplyTemplate "templates/default.html" (pageCtx baseUrl wasmRootfsUrl)
          >>= applyBaseUrl baseUrl

    -- Render all extracted Haskell chapters and dependent-base reference sources under /Source/.
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

    -- Auto-generated /Source/ index page listing book chapters and dependent-base modules.
    create ["Source/index.html"] $ do
      route idRoute
      compile $ do
        chapterIds <- sort . map toFilePath <$> getMatches "hs/PLFH/**.hs"
        depBaseIds <- sort . map toFilePath <$> getMatches "reference/dependent-base/**.hs"
        let chapMods = [p | p <- chapterIds, sourceChapterUrl p /= Nothing]
            md = buildSourceIndexMarkdown chapMods depBaseIds
            ctx =
              constField "title" "Source Browser"
                <> constField "prevUrl" "/DependentBase/"
                <> constField "nextUrl" "/Status/"
                <> pageCtx baseUrl wasmRootfsUrl
        pandocItem <- readPandocWith plfhReaderOpts (Item (fromFilePath "source-index.md") md)
        makeItem (itemBody (writePandoc pandocItem))
          >>= loadAndApplyTemplate "templates/page.html" ctx
          >>= loadAndApplyTemplate "templates/default.html" ctx
          >>= applyBaseUrl baseUrl

sourcePatterns :: Pattern
sourcePatterns =
  ("hs/PLFH/**.hs" .&&. complement internalClientPatterns)
    .||. "reference/dependent-base/**.hs"

internalClientPatterns :: Pattern
internalClientPatterns =
  fromList
    [ "hs/PLFH/Part1/AnyWitnessIso.hs"
    , "hs/PLFH/Part1/InductionClient.hs"
    , "hs/PLFH/Part1/ListsProof.hs"
    , "hs/PLFH/Part2/BigStepFunctional.hs"
    , "hs/PLFH/Part2/BisimulationRenaming.hs"
    , "hs/PLFH/RuntimeSmokeTest.hs"
    ]

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
-- @reference/dependent-base/Data/Nat/Dependent.hs@ -> @Source/dependent-base/Data/Nat/Dependent/index.html@.
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
    . enableExtension Ext_fenced_divs
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
    <> constField "repoUrl" "https://github.com/TharkunAB/PLFH"
    <> constField "repoBranch" "main"
    <> constField "plfaUrl" "https://plfa.inf.ed.ac.uk/"
    <> constField "licenseName" "Creative Commons Attribution 4.0 International License"
    <> constField "licenseUrl" "https://creativecommons.org/licenses/by/4.0/"
    <> constField "ogImageUrl" (siteOrigin ++ "/images/og-dependent-haskell.png")
    <> field "ogDescription" mkOgDescription
    <> field "canonicalUrl" mkCanonicalUrl
    <> field "showChapterNav" mkShowChapterNav
    <> field "navOverview" (mkNavActive "Overview/index.html")
    <> field "navBook" mkNavActiveBook
    <> field "navPlayground" (mkNavActive "Playground/index.html")
    <> field "navDepBase" (mkNavActive "DependentBase/index.html")
    <> field "navSetup" (mkNavActive "Setup/index.html")
    <> field "prevUrl" (mkNavUrl "prev")
    <> field "nextUrl" (mkNavUrl "next")
    <> field "srcUrl" mkSrcUrl
    <> field "moduleSrcUrl" mkModuleSrcUrl
    <> field "wasmInteractive" mkWasmInteractive
    <> field "plfaEditionLabel" (mkDefaultMeta "plfaEdition" "PLFA")
    <> field "plfaAuthorsLabel" (mkDefaultMeta "plfaAuthors" "Philip Wadler, Wen Kokke, and Jeremy G. Siek")
    <> defaultContext

mkCanonicalUrl :: Item a -> Compiler String
mkCanonicalUrl item = do
  mRoute <- getRoute (itemIdentifier item)
  let rel = case mRoute of
        Nothing -> "/"
        Just "index.html" -> "/"
        Just r
          | "/index.html" `isSuffixOf` r -> "/" ++ take (length r - length ("index.html" :: String)) r
          | otherwise                    -> "/" ++ r
  pure (siteOrigin ++ rel)

sourceCtx :: FilePath -> String -> String -> Context String
sourceCtx path baseUrl wasmRootfsUrl =
  constField "title" (sourceDisplayTitle path)
    <> constField "relPath" (sourceDisplayPath path)
    <> constField "githubUrl" (sourceGitHubUrl path)
    <> maybe mempty (constField "chapterUrl") (sourceChapterUrl path)
    <> (if "reference/dependent-base/" `isPrefixOf` path
          then constField "depBaseRefUrl" "/DependentBase/"
          else mempty)
    <> pageCtx baseUrl wasmRootfsUrl

sourceDisplayTitle :: FilePath -> String
sourceDisplayTitle path
  | "hs/PLFH/" `isPrefixOf` path =
      intercalate "." (splitDirectories (dropExtension (drop 3 path)))
  | "reference/dependent-base/" `isPrefixOf` path =
      intercalate "." (splitDirectories (dropExtension (drop 25 path)))
  | otherwise = takeFileName path

sourceDisplayPath :: FilePath -> String
sourceDisplayPath path
  | "reference/dependent-base/" `isPrefixOf` path =
      "TharkunAB/dependent-base: src/" ++ drop 25 path
  | otherwise = path

sourceGitHubUrl :: FilePath -> String
sourceGitHubUrl path
  | "reference/dependent-base/" `isPrefixOf` path =
      "https://github.com/TharkunAB/dependent-base/blob/main/src/" ++ drop 25 path
  | otherwise = "https://github.com/TharkunAB/PLFH/blob/main/" ++ path

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

buildSourceIndexMarkdown :: [FilePath] -> [FilePath] -> String
buildSourceIndexMarkdown chapMods depBaseIds =
  unlines $
    [ "Browse the Haskell modules for each chapter of PLFH and the"
    , "[`dependent-base`](https://github.com/TharkunAB/dependent-base) standard library."
    , ""
    , "Compiler plugins live in separate repositories:"
    , "[`TharkunAB/dependent-proof-search`](https://github.com/TharkunAB/dependent-proof-search)"
    , "and [`TharkunAB/dependent-obs-eq`](https://github.com/TharkunAB/dependent-obs-eq)."
    , ""
    , "## Chapter modules (" ++ show (length chapMods) ++ ")"
    , ""
    ]
      ++ map formatChapterRow chapMods
      ++ [ ""
         , "## `dependent-base` modules (" ++ show (length depBaseIds) ++ ")"
         , ""
         , "See the [`dependent-base` Reference](/DependentBase/) for the exported API summary."
         , ""
         ]
      ++ map formatPlainRow depBaseIds
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

-- | Build a per-page OpenGraph description from frontmatter metadata.
mkOgDescription :: Item a -> Compiler String
mkOgDescription item = do
  mDesc <- getMetadataField (itemIdentifier item) "description"
  case mDesc of
    Just d -> pure d
    Nothing -> do
      mTitle <- getMetadataField (itemIdentifier item) "title"
      mMod <- getMetadataField (itemIdentifier item) "module"
      case (mTitle, mMod) of
        (Just t, Just modName) ->
          pure (t ++ " (" ++ modName ++ "): checked Dependent Haskell chapter in Programming Language Foundations in Haskell (PLFH).")
        (Just t, Nothing) ->
          pure (t ++ ": Programming Language Foundations in Haskell (PLFH), checked with GHC -XDependentTypes.")
        _ -> pure defaultDescription

-- | Show chapter navigation on every page except the book table of contents.
mkShowChapterNav :: Item a -> Compiler String
mkShowChapterNav item = do
  mPrev <- getMetadataField (itemIdentifier item) "prev"
  mNext <- getMetadataField (itemIdentifier item) "next"
  mMod <- getMetadataField (itemIdentifier item) "module"
  mRoute <- getRoute (itemIdentifier item)
  case (mPrev, mNext, mMod, mRoute) of
    (Nothing, Nothing, Nothing, Just "index.html") -> noResult "Hide nav on index"
    _ -> pure "true"

-- | Mark a top-bar navigation link as active when its target route matches.
mkNavActive :: FilePath -> Item a -> Compiler String
mkNavActive target item = do
  mRoute <- getRoute (itemIdentifier item)
  if mRoute == Just target then pure "true" else noResult "Not active nav item"

-- | Mark "The Book" navigation link as active on book chapters and index pages.
mkNavActiveBook :: Item a -> Compiler String
mkNavActiveBook item = do
  mRoute <- getRoute (itemIdentifier item)
  let nonBook =
        [ Just "Overview/index.html"
        , Just "Playground/index.html"
        , Just "DependentBase/index.html"
        , Just "Setup/index.html"
        ]
  if mRoute `elem` nonBook then noResult "Not book section" else pure "true"

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
    Just rel -> pure ("https://github.com/TharkunAB/PLFH/blob/main/" ++ rel)

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
