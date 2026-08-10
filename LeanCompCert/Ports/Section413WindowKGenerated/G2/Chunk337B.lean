import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk337A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk337B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk337A

def state06 : KState := ⟨⟨360590643646390466, 360590650569879969⟩, ⟨(-316177134168445027), (-316019099012201031)⟩, true⟩

def words05 : List Nat := [360581280474261382, 360581282239522168, 360581283563186358, 360581284908589999, 360581285845808885, 360581286783091942, 360581288596504129, 360581289536419672, 360581289814110328, 360581290091842820]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 33750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 33700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360633674119514926, 360633681047273335⟩, ⟨(-1769320309815746006), (-1769162130520116540)⟩, true⟩

def words06 : List Nat := [360581290092216142, 360581290366754084, 360581291200466548, 360581292034215886, 360581292119921600, 360581292120373148, 360581291420709180, 360581291509139899, 360581292473201545, 360581294024960697]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 33760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 33700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360611168621227292, 360611175553280012⟩, ⟨(-1009097593694148316), (-1008939269358031992)⟩, true⟩

def words07 : List Nat := [360581295135502181, 360581296246027263, 360581298231987248, 360581300778133898, 360581302710789799, 360581304643398030, 360581306118456654, 360581306720599538, 360581307605182204, 360581308489860989]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 33770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 33700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587367168953997, 360587374105266901⟩, ⟨(-204966059934523890), (-204807591668097606)⟩, true⟩

def words08 : List Nat := [360581309167540114, 360581310196873191, 360581310785461953, 360581311374065495, 360581311544314896, 360581312155063217, 360581312632116807, 360581313109226401, 360581313109635818, 360581313095185279]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 33780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 33700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360661346390137026, 360661353330714852⟩, ⟨(-2705156355552820740), (-2704997743153598734)⟩, true⟩

def words09 : List Nat := [360581314149698542, 360581315204284921, 360581316839361652, 360581317898819044, 360581318211905885, 360581318525014804, 360581319712485835, 360581321443043338, 360581323811216201, 360581326179353840]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 33790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 33700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 33700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk337B
