import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk914A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk914B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk914A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk914B
