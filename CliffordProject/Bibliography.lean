import VersoManual.Bibliography
import VersoBlueprint.Cite

open Verso.Genre.Manual.Bibliography

-- @[bib "Appleby"]
-- def Appleby : Citable := .article
--   {
--     title := inlines!"Symmetric informationally complete-positive operator valued measures and the extended Clifford group"
--     authors := #[inlines!"D. M. Appleby"]
--     journal := inlines!"Journal of Mathematical Physics"
--     year := 2005
--     month := some (inlines!"4")
--     volume := inlines!"46"
--     number := inlines!"5"
--     pages := some (052107, 052107)
--     url := "https://doi.org/10.1063/1.1896384"
--   }

@[bib "Appleby"]
def Appleby : Citable := .arXiv
  {
    title := inlines!"SIC-POVMs and the Extended Clifford Group"
    authors := #[inlines!"D. M. Appleby"]
    year := 2005
    id := "quant-ph/0412001"
  }
