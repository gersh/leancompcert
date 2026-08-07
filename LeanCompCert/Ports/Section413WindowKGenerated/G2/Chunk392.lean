import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk392

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360582395956352403, 360582405405976636⟩, ⟨(-4648617076317925), (-4398244791980945)⟩, true⟩

def state01 : KState := ⟨⟨360576532732382131, 360576542187053986⟩, ⟨225034164522323682, 225284734698352046⟩, true⟩

def words00 : List Nat := [360582293209188889, 360582292853135419, 360582292284756704, 360582292252396782, 360582292219888400, 360582292022739571, 360582291177938616, 360582289829184432, 360582288480394649, 360582287780899902]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360544029252407813, 360544038712071350⟩, ⟨1499808224680231039, 1500058990605514847⟩, true⟩

def words01 : List Nat := [360582287989826776, 360582288345367169, 360582288374564361, 360582288419016779, 360582288419464625, 360582287898033735, 360582287503272102, 360582287503802563, 360582286983803329, 360582286009129115]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595368015053530, 360595377479730574⟩, ⟨(-514105992690591368), (-513855030110371458)⟩, true⟩

def words02 : List Nat := [360582285034393653, 360582283779923456, 360582282854154885, 360582282377726460, 360582281901281490, 360582280871172411, 360582279744127767, 360582279265788813, 360582278956874260, 360582279291305340]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592960067791099, 360592969537525618⟩, ⟨(-419637104523282648), (-419385943513682976)⟩, true⟩

def words03 : List Nat := [360582279292332938, 360582279293413652, 360582279942743585, 360582281003869739, 360582281508026714, 360582282012237286, 360582282012713861, 360582281924720607, 360582281821738778, 360582282094710357]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360603166410193437, 360603175884932920⟩, ⟨(-820101330747524383), (-819849973318446963)⟩, true⟩

def words04 : List Nat := [360582283015595325, 360582283951194698, 360582284504674248, 360582285058183561, 360582285333902541, 360582285982556629, 360582286822038516, 360582287661580781, 360582287986973317, 360582288519685705]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk392
