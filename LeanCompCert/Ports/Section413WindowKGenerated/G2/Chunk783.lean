import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk783

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360576185788837307, 360576225655094999⟩, ⟨470303853891756298, 472412124343742588⟩, true⟩

def state01 : KState := ⟨⟨360599416295363044, 360599456172161431⟩, ⟨(-1348724437484341472), (-1346615341644399186)⟩, true⟩

def words00 : List Nat := [360582259025246576, 360582259196400865, 360582259269124530, 360582259341967705, 360582259373902595, 360582259499357511, 360582259787347201, 360582260075543599, 360582260214654911, 360582260435398468]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 78300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 78300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360620763923972009, 360620803811330061⟩, ⟨(-3020572024787039045), (-3018462101968146559)⟩, true⟩

def words01 : List Nat := [360582260818737012, 360582261202399789, 360582261704106242, 360582262043360366, 360582262224505408, 360582262405750519, 360582262749584618, 360582263198397270, 360582263691395645, 360582264184640308]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 78310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 78300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360584402798093361, 360584442696109670⟩, ⟨(-172694612472115051), (-170583854846323341)⟩, true⟩

def words02 : List Nat := [360582264596151380, 360582264845145096, 360582265052081410, 360582265259325023, 360582265374052798, 360582265375171282, 360582265327341128, 360582265195287911, 360582265063025409, 360582264965009004]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 78320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 78300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558533072263342, 360558572980812188⟩, ⟨1853825787706579258, 1855937370400400264⟩, true⟩

def words03 : List Nat := [360582265019235585, 360582265073668813, 360582265074665652, 360582265047580517, 360582264910164285, 360582264732416691, 360582264554348989, 360582264303256958, 360582264083324069, 360582263782068257]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 78330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 78300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360597434094336278, 360597474013436330⟩, ⟨(-1193844316817581975), (-1191731907488510143)⟩, true⟩

def words04 : List Nat := [360582263480566626, 360582263342131650, 360582263443138315, 360582263559943079, 360582263560984759, 360582263540286304, 360582263456838939, 360582263497245166, 360582263649705171, 360582263844995743]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 78340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 78300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360593340988129746, 360593380917903067⟩, ⟨(-873217662891099753), (-871104417259427539)⟩, true⟩

def words05 : List Nat := [360582263896439135, 360582263947980467, 360582263948893690, 360582264024764984, 360582264064249635, 360582264103918034, 360582264104915089, 360582264076338338, 360582264219111876, 360582264362253453]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 78350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 78300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360592881197392827, 360592921137699916⟩, ⟨(-837257469088315297), (-835143397978006279)⟩, true⟩

def words06 : List Nat := [360582264580728765, 360582264636932953, 360582264637939415, 360582264612032315, 360582264585946950, 360582264447607251, 360582264547478569, 360582264679382124, 360582264719567810, 360582264856703400]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 78360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 78300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602232004632009, 360602271955518438⟩, ⟨(-1570100052400911611), (-1567985152136059405)⟩, true⟩

def words07 : List Nat := [360582265126090927, 360582265395833153, 360582265800551083, 360582266083985584, 360582266214562692, 360582266345212970, 360582266523927657, 360582266784297724, 360582267040451508, 360582267296836665]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 78370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 78300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360603531771338221, 360603571732896502⟩, ⟨(-1672102277424043294), (-1669986540649509044)⟩, true⟩

def words08 : List Nat := [360582267472136525, 360582267485141535, 360582267623369244, 360582267761923785, 360582267833329808, 360582267990086913, 360582268013824326, 360582268037679277, 360582268165576992, 360582268438632499]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 78380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 78300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578145469338717, 360578185441449441⟩, ⟨318136875817676138, 320253439851759774⟩, true⟩

def words09 : List Nat := [360582268849946003, 360582269261463834, 360582269547697399, 360582269764265811, 360582269940089129, 360582270116205068, 360582270317506711, 360582270356668652, 360582270357676407, 360582270306753673]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 78390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 78300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 78300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk783
