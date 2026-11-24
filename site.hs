{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Data.List (isPrefixOf)
import Data.Maybe (fromMaybe)
import Hakyll
import System.Environment (lookupEnv)
import System.FilePath (dropExtension, takeBaseName, (</>))
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
  hakyll $ do
    match "css/*" $ do
      route idRoute
      compile compressCssCompiler

    match "templates/*" $ compile templateBodyCompiler

    match "content/index.md" $ do
      route $ constRoute "index.html"
      compile $
        plfhPandocCompiler
          >>= loadAndApplyTemplate "templates/page.html" (pageCtx baseUrl)
          >>= loadAndApplyTemplate "templates/default.html" (pageCtx baseUrl)
          >>= applyBaseUrl baseUrl

    match (fromList
      [ "content/Preface.md"
      , "content/Setup.md"
      , "content/Status.md"
      , "content/Citing.md"
      ] .||. "content/part1/*.md" .||. "content/part2/*.md") $ do
      route prettyPageRoute
      compile $
        plfhPandocCompiler
          >>= loadAndApplyTemplate "templates/page.html" (pageCtx baseUrl)
          >>= loadAndApplyTemplate "templates/default.html" (pageCtx baseUrl)
          >>= applyBaseUrl baseUrl

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

-- | Compile Markdown with Pandoc + Skylighting, with TeX math disabled
-- (PLFH uses Unicode and clean HTML/CSS rather than heavy TeX/KaTeX).
plfhPandocCompiler :: Compiler (Item String)
plfhPandocCompiler =
  pandocCompilerWith readerOpts defaultHakyllWriterOptions
  where
    readerOpts = defaultHakyllReaderOptions
      { readerExtensions = plfhMarkdownExtensions
      }

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

pageCtx :: String -> Context String
pageCtx baseUrl =
  constField "baseurl" baseUrl
    <> constField "siteTitle" "Programming Language Foundations in Haskell"
    <> constField "repoUrl" "https://github.com/Tritlo/PLFH"
    <> constField "repoBranch" "main"
    <> constField "plfaUrl" "https://plfa.inf.ed.ac.uk/19.08/"
    <> constField "licenseName" "Creative Commons Attribution 4.0 International License"
    <> constField "licenseUrl" "https://creativecommons.org/licenses/by/4.0/"
    <> field "prevUrl" (mkNavUrl "prev")
    <> field "nextUrl" (mkNavUrl "next")
    <> field "srcUrl" mkSrcUrl
    <> defaultContext

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
