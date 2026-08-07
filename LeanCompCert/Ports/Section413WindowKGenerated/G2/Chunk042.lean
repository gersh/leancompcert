import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk042

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360262232067052750, 360262232154654541⟩, ⟨1304497342191315062, 1304497592095527280⟩, true⟩

def state01 : KState := ⟨⟨360271178042863531, 360271178130904012⟩, ⟨1267757496044780852, 1267757747793748436⟩, true⟩

def words00 : List Nat := [360572752885969589, 360572735101440175, 360572713177235343, 360572663469838293, 360572613786075840, 360572539421160620, 360572493855394841, 360572444868654418, 360572395905186209, 360572308237268323]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 4200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 4200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361027955603600771, 361027955692082838⟩, ⟨(-1922938590794027721), (-1922938337183803581)⟩, true⟩

def words01 : List Nat := [360572236726950895, 360572221120542868, 360572205521529693, 360572198860590585, 360572198860633692, 360572154899410432, 360572122769431564, 360572175095366019, 360572283100284753, 360572391054038820]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 4210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 4200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360654521396404079, 360654521485333245⟩, ⟨(-347955755373271348), (-347955499874102706)⟩, true⟩

def words02 : List Nat := [360572451292587059, 360572456525926883, 360572486297793109, 360572516055579897, 360572516055619415, 360572515617653133, 360572460254230668, 360572375822944894, 360572291431579247, 360572281943883446]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 4220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 4200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360327718074902262, 360327718164273560⟩, ⟨1037074256284190908, 1037074513655814486⟩, true⟩

def words03 : List Nat := [360572356772508538, 360572431565787625, 360572467519742636, 360572483062165738, 360572483062206005, 360572447838396972, 360572412631201338, 360572395985303426, 360572368910546277, 360572311209947102]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 4230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 4200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361008140733416292, 361008140823232276⟩, ⟨(-1850170985067306127), (-1850170725807995813)⟩, true⟩

def words04 : List Nat := [360572253536548402, 360572293770825724, 360572391605397966, 360572489393885048, 360572541283851595, 360572588509257208, 360572662322262473, 360572736100538018, 360572806534758023, 360572908942308260]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 4240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 4200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360867110889662264, 360867110979927632⟩, ⟨(-1249933175308162472), (-1249932914136714558)⟩, true⟩

def words05 : List Nat := [360572977402090390, 360573045829683797, 360573169107565394, 360573320411508801, 360573434391825037, 360573548318600093, 360573616480759154, 360573630605537259, 360573699497682267, 360573768357506437]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 4250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 4200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360846342386578508, 360846342477290109⟩, ⟨(-1162131945428764526), (-1162131682354139178)⟩, true⟩

def words06 : List Nat := [360573891933454216, 360573961495714335, 360573984624098369, 360574007741641324, 360574015544827918, 360574053305924477, 360574105280520166, 360574157230775183, 360574180490740614, 360574244214036975]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 4260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 4200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360954548583874608, 360954548675033409⟩, ⟨(-1623886806528986379), (-1623886541542594153)⟩, true⟩

def words07 : List Nat := [360574362360824385, 360574480452326196, 360574652916561699, 360574771558839567, 360574844953758908, 360574918314360699, 360574964619092622, 360575047263040371, 360575135931633311, 360575224558812294]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 4270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 4200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360877021038327482, 360877021129938823⟩, ⟨(-1293977066594746890), (-1293976799669260754)⟩, true⟩

def words08 : List Nat := [360575284679489631, 360575291144949322, 360575351784961509, 360575412396685393, 360575457936785406, 360575457936832924, 360575449877787697, 360575413509880481, 360575394836255057, 360575465129083717]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 4280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 4200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360718725163257156, 360718725255317234⟩, ⟨(-614522745084744652), (-614522476231893240)⟩, true⟩

def words09 : List Nat := [360575532213021698, 360575599265715418, 360575635924039184, 360575654241086885, 360575657715341988, 360575661187992490, 360575718451705854, 360575779808323352, 360575813051493042, 360575846279211237]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 4290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 4200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 4200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk042
