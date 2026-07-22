import VersoManual
import VersoBlueprint.PreviewManifest
import CliffordProject.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  -- Informal.PreviewManifest.manualMainWithPreviewData
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc CliffordProject.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
