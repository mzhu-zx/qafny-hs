module Qafny.Utils.Path where
import           System.Directory
import           System.FilePath

makeRelativePath :: FilePath -> FilePath -> IO FilePath
makeRelativePath anchor path = do
  anchors <- splitPath . normalise <$> makeAbsolute anchor
  paths   <- splitPath . normalise <$> makeAbsolute (dropFileName path)
  putStrLn $ (show anchors) ++ (show paths)
  let (anchorsR, pathsR) = diffPath anchors paths
  putStrLn $ (show anchorsR) ++ (show pathsR)
  pure $ joinPath (("../" <$ pathsR) ++ anchorsR)

diffPath :: (Eq a) => [a] -> [a] -> ([a], [a])
diffPath xs'@(x:xs) ys'@(y:ys)
  | x == y    = diffPath xs ys
  | otherwise = (xs', ys')
diffPath xs ys = (xs, ys)


