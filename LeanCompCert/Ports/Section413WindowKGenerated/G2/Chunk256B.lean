import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk256A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk256B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk256A

def state06 : KState := ⟨⟨360497974443549612, 360497978350548922⟩, ⟨2189591110559187684, 2189658928303982364⟩, true⟩

def words05 : List Nat := [360583325612303064, 360583326104586006, 360583326104886032, 360583325541895316, 360583324015939078, 360583321438544829, 360583318861253657, 360583317800040380, 360583315227254588, 360583311901924760]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360552945811678697, 360552949721855240⟩, ⟨778838497256194868, 778906396543758126⟩, true⟩

def words06 : List Nat := [360583308576778619, 360583306273373081, 360583305201786663, 360583304346369473, 360583303490993212, 360583301208647700, 360583298104263734, 360583296514679329, 360583294925121949, 360583292783660607]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360574597886005474, 360574601799381274⟩, ⟨222884512296257102, 222952493724532414⟩, true⟩

def words07 : List Nat := [360583291601962622, 360583289554505244, 360583287507143361, 360583287602560723, 360583287602843859, 360583287306498145, 360583287010136202, 360583285939212053, 360583284087783940, 360583283750071482]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360547319708877039, 360547323625424185⟩, ⟨923348129020542039, 923416191905185633⟩, true⟩

def words08 : List Nat := [360583284081594105, 360583284081930262, 360583283242721948, 360583281235756743, 360583279228895075, 360583276247013382, 360583274056114333, 360583272360398616, 360583270664776169, 360583268202765765]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360591404017865555, 360591407937584289⟩, ⟨(-209415030629418661), (-209346886250479355)⟩, true⟩

def words09 : List Nat := [360583266803926721, 360583266105729415, 360583266220698072, 360583266264653434, 360583266264966432, 360583264988897830, 360583263712866882, 360583262393086330, 360583262143996540, 360583262461289574]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk256B
