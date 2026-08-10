import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk287A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk287B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk287A

def state06 : KState := ⟨⟨360723426140393564, 360723431097181925⟩, ⟨(-4049248455616970333), (-4049152039892616241)⟩, true⟩

def words05 : List Nat := [360582615012705529, 360582617241135454, 360582620675963320, 360582623934252110, 360582626131184080, 360582628327997678, 360582631410734482, 360582635100797109, 360582639996653616, 360582644892255372]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360663344779652136, 360663349740063991⟩, ⟨(-2321301945897605035), (-2321205425944092295)⟩, true⟩

def words06 : List Nat := [360582649183086968, 360582652638174815, 360582656013802225, 360582659389305615, 360582661968752567, 360582664044282723, 360582665342799712, 360582666641268353, 360582668285819605, 360582671090522992]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360576904115934833, 360576909079920847⟩, ⟨166271939690307215, 166368562490962993⟩, true⟩

def words07 : List Nat := [360582675100122464, 360582679109515856, 360582682343725464, 360582684378486643, 360582686094084114, 360582687809665166, 360582689494718999, 360582689980627095, 360582689980965812, 360582689780493848]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360638437104976944, 360638442072551664⟩, ⟨(-1604956124082520628), (-1604859397981296136)⟩, true⟩

def words08 : List Nat := [360582689780762881, 360582690845337125, 360582692802217700, 360582694759041440, 360582695674240319, 360582695932702063, 360582696364653774, 360582696796684585, 360582698432075494, 360582700368617057]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360669522748634778, 360669527719840551⟩, ⟨(-2500203981581323259), (-2500107150924109241)⟩, true⟩

def words09 : List Nat := [360582701380867574, 360582702393080420, 360582704608400828, 360582707428505108, 360582709581552818, 360582711734512039, 360582713117514326, 360582715428705324, 360582718443328963, 360582721457873116]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk287B
