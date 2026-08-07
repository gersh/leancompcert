import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk439

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360557230707064552, 360557242668668779⟩, ⟨1139519985573239501, 1139874851460588065⟩, true⟩

def state01 : KState := ⟨⟨360567688998917625, 360567700966180783⟩, ⟨680310206510756400, 680665320853470146⟩, true⟩

def words00 : List Nat := [360583207336284296, 360583206568201754, 360583206070700612, 360583205900246652, 360583205729743172, 360583205121792279, 360583204244642671, 360583203534693032, 360583202824601102, 360583202339919191]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 43900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 43900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360579405830359721, 360579417803347319⟩, ⟨165705195724754901, 166060561455566417⟩, true⟩

def words01 : List Nat := [360583201987451360, 360583201128011142, 360583200268491264, 360583199927150920, 360583199922037260, 360583199784448561, 360583199646800651, 360583199248563945, 360583198866922083, 360583198781522537]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 43910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 43900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360552887969236096, 360552899947870899⟩, ⟨1330441337472627726, 1330796951256864344⟩, true⟩

def words02 : List Nat := [360583199010581046, 360583199011180933, 360583198809560416, 360583198216274921, 360583197622927766, 360583196657505474, 360583195952725487, 360583195229656667, 360583194506557839, 360583193527457898]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 43920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 43900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360595366226180274, 360595378210485557⟩, ⟨(-535790980483082358), (-535435117566627756)⟩, true⟩

def words03 : List Nat := [360583192838371179, 360583192550280886, 360583192490707948, 360583192648725822, 360583192649279533, 360583192330773724, 360583192044268453, 360583192335370608, 360583192613194073, 360583192891135369]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 43930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 43900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594643952243809, 360594655942260494⟩, ⟨(-504251097948143353), (-503894984044878437)⟩, true⟩

def words04 : List Nat := [360583192891670044, 360583192842174378, 360583192511507982, 360583192605186342, 360583192605693572, 360583192216732298, 360583192001667156, 360583191464328691, 360583190926899835, 360583191015773159]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 43940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 43900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk439
