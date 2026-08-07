import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk251

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587343667076353, 360587347398206008⟩, ⟨(-87785135382047430), (-87721781393052418)⟩, true⟩

def state01 : KState := ⟨⟨360547236241952455, 360547239976212676⟩, ⟨919111902551190080, 919175335132688390⟩, true⟩

def words00 : List Nat := [360583852646045189, 360583852270470242, 360583852998884845, 360583853727335909, 360583854051529370, 360583854051857441, 360583852797614503, 360583850744307782, 360583848691107348, 360583845923450139]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 25100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 25100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360529778158825677, 360529781896176643⟩, ⟨1357700651585217444, 1357764161790816028⟩, true⟩

def words01 : List Nat := [360583844589612650, 360583844713593435, 360583844713887834, 360583843638234191, 360583841768588933, 360583839495842014, 360583837223172066, 360583836531410362, 360583835168729681, 360583833017267042]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 25110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 25100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360608591402390170, 360608595142844551⟩, ⟨(-622536273639727475), (-622472685461021341)⟩, true⟩

def words02 : List Nat := [360583830865901765, 360583830680464679, 360583830680735072, 360583830425714785, 360583830170687458, 360583828502386962, 360583826338656566, 360583825754962101, 360583825171216300, 360583826025600470]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 25120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 25100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360558130209980630, 360558133953559366⟩, ⟨645906295334064780, 645969962043235486⟩, true⟩

def words03 : List Nat := [360583826213159415, 360583826400739293, 360583827480385600, 360583829616168078, 360583830709029474, 360583831801855582, 360583831802156956, 360583831629500322, 360583829882301030, 360583828860561882]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 25130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 25100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579536890489884, 360579540637163194⟩, ⟨107563126560610672, 107626871082679268⟩, true⟩

def words04 : List Nat := [360583827838795927, 360583827735568475, 360583827202789244, 360583825424157982, 360583823645609286, 360583821188415404, 360583820290522398, 360583820630293908, 360583820630586793, 360583820035615786]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 25140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 25100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360611950491189340, 360611954240969532⟩, ⟨(-707992043342666313), (-707928220667259273)⟩, true⟩

def words05 : List Nat := [360583819865738074, 360583819650954347, 360583820797336539, 360583820797665222, 360583820586598961, 360583819030703252, 360583817474869663, 360583816147732630, 360583817188932504, 360583818307554038]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 25150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 25100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601344565954465, 360601348318863807⟩, ⟨(-441394311241487864), (-441330409820870440)⟩, true⟩

def words06 : List Nat := [360583818629639222, 360583818629968446, 360583819512334465, 360583820741114098, 360583820878923440, 360583820879252276, 360583819445877553, 360583817216850389, 360583814987933975, 360583815030165668]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 25160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 25100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360514931539200658, 360514935295210889⟩, ⟨1734390537717297737, 1734454517202734587⟩, true⟩

def words07 : List Nat := [360583817301114244, 360583819571951276, 360583821058426223, 360583821702793209, 360583821703069560, 360583821481275390, 360583821543931585, 360583821544260518, 360583820259213870, 360583817523852777]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 25170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 25100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360644432605364636, 360644436364480094⟩, ⟨(-1527279954333674739), (-1527215896643298883)⟩, true⟩

def words08 : List Nat := [360583814788636049, 360583812341662208, 360583810711562827, 360583810654231340, 360583810596879288, 360583809068270912, 360583807667763111, 360583807421403371, 360583808500038699, 360583810907108680]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 25180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 25100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360609693221613468, 360609696983871697⟩, ⟨(-652089365905828298), (-652025229034271980)⟩, true⟩

def words09 : List Nat := [360583812493920456, 360583814080639280, 360583815142789644, 360583817443002422, 360583819341873281, 360583821240647014, 360583822062326929, 360583822062656401, 360583822966461095, 360583823993552493]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 25190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 25100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 25100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk251
