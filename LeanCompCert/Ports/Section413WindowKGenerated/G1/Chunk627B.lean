import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk627A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk627B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk627A

def state06 : KState := ⟨⟨362483267212179730, 362483325169419439⟩, ⟨127983391912576681, 130440267421035231⟩, true⟩

def words05 : List Nat := [371285403091668537, 371285403112231999, 371285403385875094, 371285403533993151, 371285403640642198, 371285403748050114, 371285403841234491, 371285403843365329, 371285403598020566, 371285403567561903]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 62750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 62700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362482919795655281, 362482977771910667⟩, ⟨149859758526396160, 152317827558100172⟩, true⟩

def words06 : List Nat := [371285403756683598, 371285403769022190, 371285403779904452, 371285403791504015, 371285403879364856, 371285403881751049, 371285404063653214, 371285404247367715, 371285404372023673, 371285404374229579]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 62760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 62700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362498243653980970, 362498301649466673⟩, ⟨(-812077035691168245), (-809617759475019161)⟩, true⟩

def words07 : List Nat := [371285404490243315, 371285404645990799, 371285405054451233, 371285405125409741, 371285405169683956, 371285405214665060, 371285405335391397, 371285405337739985, 371285405537510659, 371285405745300206]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 62770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 62700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473333320936816, 362473391335698677⟩, ⟨751842215109637270, 754302701576965102⟩, true⟩

def words08 : List Nat := [371285405921153794, 371285405923285411, 371285405760915455, 371285405704544260, 371285405647066612, 371285405636660145, 371285405287667913, 371285404938517294, 371285404588515178, 371285404438128634]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 62780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 62700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362459249636715809, 362459307670670825⟩, ⟨1636316999308531067, 1638778691013105139⟩, true⟩

def words09 : List Nat := [371285404310580526, 371285404375236555, 371285404440505995, 371285404442638433, 371285404169839521, 371285403961818128, 371285403752746770, 371285403649240994, 371285403285865191, 371285402872757021]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 62790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 62700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 62700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk627B
