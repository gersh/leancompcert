import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk392A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk392B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk392A

def state06 : KState := ⟨⟨360626864389546486, 360626873869298356⟩, ⟨(-1750305793571099579), (-1750054239380585885)⟩, true⟩

def words05 : List Nat := [360582289700082196, 360582290880573989, 360582292276744832, 360582293395145719, 360582293958516192, 360582294521908609, 360582295455631068, 360582296720668803, 360582297856535651, 360582298992464333]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601249157854401, 360601258642670566⟩, ⟨(-744838422282869888), (-744586669244097770)⟩, true⟩

def words06 : List Nat := [360582299703260914, 360582299972875661, 360582300065405480, 360582300158078566, 360582300158523271, 360582300086954597, 360582299670803636, 360582298929638948, 360582298188410441, 360582298425990469]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360544204641392815, 360544214131207816⟩, ⟨1495715320175091582, 1495967269543567554⟩, true⟩

def words07 : List Nat := [360582299400400927, 360582300374863494, 360582300879111965, 360582300940868739, 360582300941314117, 360582300833745020, 360582300726028204, 360582300451444441, 360582299806706989, 360582298837662592]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582666794812478, 360582676289643748⟩, ⟨(-15294508800964398), (-15042362368641608)⟩, true⟩

def words08 : List Nat := [360582297868550130, 360582296996984397, 360582296450229967, 360582296391601492, 360582296332929497, 360582295677453478, 360582294836734693, 360582294212392305, 360582293587926108, 360582293444657145]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360591111140741248, 360591120640643767⟩, ⟨(-347133981312706075), (-346881635606540629)⟩, true⟩

def words09 : List Nat := [360582293445138930, 360582292955187154, 360582292621018452, 360582293245744524, 360582293563980342, 360582293882286337, 360582293882760059, 360582293910283202, 360582294135314037, 360582294360508236]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk392B
