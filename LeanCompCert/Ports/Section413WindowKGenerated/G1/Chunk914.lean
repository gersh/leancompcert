import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk914

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492125032936968, 362492251594089350⟩, ⟨(-660842890557392888), (-653032649207284246)⟩, true⟩

def state01 : KState := ⟨⟨362482538619492090, 362482665209461518⟩, ⟨215373418304698535, 223186293680120415⟩, true⟩

def words00 : List Nat := [371285106975311174, 371285106978509074, 371285106940083448, 371285106954606275, 371285106992996742, 371285106996245899, 371285106935146246, 371285106875015203, 371285106813551064, 371285106805497840]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 91400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 91400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362476686250834596, 362476812869535780⟩, ⟨750407564425071067, 758223066318936785⟩, true⟩

def words01 : List Nat := [371285106873851591, 371285106970184605, 371285107040806188, 371285107044000057, 371285106954946833, 371285106896365868, 371285106884537515, 371285106887732744, 371285106798974301, 371285106711871363]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 91410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 91400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362477791631054294, 362477918278338983⟩, ⟨649381564975954191, 657199680119822755⟩, true⟩

def words02 : List Nat := [371285106623330704, 371285106597369676, 371285106542069601, 371285106576637229, 371285106582596314, 371285106585799277, 371285106469317855, 371285106384175589, 371285106297415260, 371285106287527650]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 91420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 91400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362483319054689636, 362483445731125239⟩, ⟨144001411279185443, 151822191836934207⟩, true⟩

def words03 : List Nat := [371285106211320996, 371285106136554611, 371285106101711931, 371285106105295027, 371285106140167649, 371285106178246355, 371285106207605634, 371285106210800456, 371285106092922425, 371285106078804996]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 91430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 91400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362474056136502435, 362474182841427272⟩, ⟨991042583343025910, 998865969103095168⟩, true⟩

def words04 : List Nat := [371285106094545032, 371285106097755172, 371285106017092472, 371285105896347513, 371285105774410086, 371285105690412961, 371285105545426795, 371285105489582540, 371285105432590248, 371285105377994830]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 91440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 91400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362499385179420322, 362499511913184540⟩, ⟨(-1325424475950249798), (-1317598452680083120)⟩, true⟩

def words05 : List Nat := [371285105260725583, 371285105255167113, 371285105358136515, 371285105364367074, 371285105366895269, 371285105348863182, 371285105427432813, 371285105469014507, 371285105628697651, 371285105789780247]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 91450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 91400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362495474887252432, 362495601649864872⟩, ⟨(-967766806759260689), (-959938144883628433)⟩, true⟩

def words06 : List Nat := [371285105946059218, 371285106020571907, 371285106213480142, 371285106408072663, 371285106606956863, 371285106714815048, 371285106822227663, 371285106930682586, 371285107078109982, 371285107196487478]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 91460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 91400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482570249395861, 362482697040825175⟩, ⟨212711139854895386, 220542437754203378⟩, true⟩

def words07 : List Nat := [371285107362836616, 371285107530521093, 371285107696892167, 371285107704804323, 371285107747939734, 371285107792750543, 371285107910971275, 371285107914168386, 371285107890381438, 371285107867648024]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 91470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 91400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362483995867210266, 362484122687277762⟩, ⟨82285692968982629, 90119610836106071⟩, true⟩

def words08 : List Nat := [371285107875438446, 371285107878961608, 371285107885666534, 371285107915765533, 371285107933048521, 371285107936245223, 371285107804723278, 371285107736004152, 371285107705342777, 371285107708710008]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 91480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 91400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362492899589403327, 362493026438549978⟩, ⟨(-732354391314333120), (-724517812851241048)⟩, true⟩

def words09 : List Nat := [371285107700333098, 371285107692839205, 371285107792537786, 371285107871003342, 371285107970616104, 371285108071478057, 371285108148084043, 371285108151302818, 371285108207156560, 371285108297624183]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 91490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 91400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 91400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk914
