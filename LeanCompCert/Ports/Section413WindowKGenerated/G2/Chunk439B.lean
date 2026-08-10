import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk439A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk439B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk439A

def state06 : KState := ⟨⟨360557657884728002, 360557669880407647⟩, ⟨1121549830633736864, 1121906193450993282⟩, true⟩

def words05 : List Nat := [360583191794080410, 360583192572467541, 360583192909787729, 360583192910388094, 360583192731597439, 360583192299864104, 360583191867963061, 360583191849374277, 360583191529345535, 360583190949412447]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 43950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 43900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360620906631657538, 360620918633001919⟩, ⟨(-1659097481135785197), (-1658740869268385769)⟩, true⟩

def words06 : List Nat := [360583190369359104, 360583190607902966, 360583191426744406, 360583192245664116, 360583192621769024, 360583193108046045, 360583193318149025, 360583193528406770, 360583194255094256, 360583195113653522]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 43960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 43900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360624302922007130, 360624314929070611⟩, ⟨(-1808379954698515121), (-1808023091333553669)⟩, true⟩

def words07 : List Nat := [360583195712260415, 360583196310905725, 360583197425935977, 360583198952198199, 360583200347615206, 360583201743067020, 360583202843739427, 360583203872817168, 360583204808073523, 360583205743482891]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 43970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 43900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360598341322476782, 360598353335201187⟩, ⟨(-666606476676400634), (-666249364315787112)⟩, true⟩

def words08 : List Nat := [360583206536571479, 360583206814343251, 360583206828665677, 360583206843047572, 360583206843551450, 360583206645697738, 360583207193258971, 360583207740920718, 360583207861418842, 360583208206326741]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 43980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 43900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360619146642195475, 360619158660593643⟩, ⟨(-1581994532419131131), (-1581637170441814245)⟩, true⟩

def words09 : List Nat := [360583209067295403, 360583209928410472, 360583210742540988, 360583211041592804, 360583211042156515, 360583210844554813, 360583210964763185, 360583211543171656, 360583212360638343, 360583213178208202]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 43990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 43900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 43900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk439B
