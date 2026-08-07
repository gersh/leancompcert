import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk321

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360605354713218169, 360605360946407940⟩, ⟨(-752276324784987554), (-752141026372539748)⟩, true⟩

def state01 : KState := ⟨⟨360626716626796283, 360626722864017356⟩, ⟨(-1438106453905690862), (-1437971026068501346)⟩, true⟩

def words00 : List Nat := [360581931876976216, 360581933295434379, 360581934020554185, 360581934745671103, 360581935228254943, 360581936201992034, 360581937836035765, 360581939470060034, 360581940209381055, 360581941604446851]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 32100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 32100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360684483908214283, 360684490149469643⟩, ⟨(-3293462134910416016), (-3293326577512088976)⟩, true⟩

def words01 : List Nat := [360581943736195403, 360581945867940595, 360581948325196972, 360581949815031197, 360581950477667239, 360581951140303320, 360581952767835855, 360581954995730877, 360581958188329451, 360581961380828814]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 32110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 32100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360606218273308656, 360606224518645613⟩, ⟨(-779509822502511628), (-779374133984282348)⟩, true⟩

def words02 : List Nat := [360581963985002311, 360581965621979762, 360581966831938112, 360581968041938682, 360581968966530983, 360581968966958768, 360581968924559526, 360581968398860109, 360581967873112436, 360581968375544425]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 32120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 32100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360495524574555607, 360495530823918079⟩, ⟨2777692279495775673, 2777828097374722011⟩, true⟩

def words03 : List Nat := [360581968856950638, 360581969338406252, 360581969338787501, 360581969337185254, 360581968368917562, 360581967159002081, 360581965949040531, 360581964714672852, 360581962513863145, 360581959825080952]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 32130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 32100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360536709938972961, 360536716192376191⟩, ⟨1454005314615364034, 1454141262383946040⟩, true⟩

def words04 : List Nat := [360581957136369490, 360581955411568898, 360581954412834555, 360581954377807403, 360581954342741423, 360581953482742357, 360581951656518449, 360581949705835977, 360581947755145854, 360581946091672737]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 32140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 32100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360526334905843283, 360526341163326134⟩, ⟨1787426804594294993, 1787562883543287621⟩, true⟩

def words05 : List Nat := [360581944685264719, 360581942528842510, 360581940372475188, 360581937960421135, 360581936175323035, 360581933952319815, 360581931729412117, 360581929005277176, 360581926314227831, 360581924586321883]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 32150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 32100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360515359519141441, 360515365780657092⟩, ⟨2140431452000998258, 2140567660665432486⟩, true⟩

def words06 : List Nat := [360581922858382098, 360581921652953223, 360581920175396918, 360581918104980656, 360581916034625425, 360581913292334096, 360581911031281525, 360581909191669078, 360581907352124365, 360581905030289217]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 32160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 32100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360536543052466014, 360536549318030978⟩, ⟨1458887361199806851, 1459023700150440721⟩, true⟩

def words07 : List Nat := [360581902962336822, 360581901537319226, 360581900112256902, 360581899649290712, 360581898221922009, 360581895858945793, 360581893496035118, 360581891566597418, 360581890182752754, 360581888774219619]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 32170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 32100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360565824916989232, 360565831186636574⟩, ⟨516067155637775884, 516203625979012148⟩, true⟩

def words08 : List Nat := [360581887365713511, 360581885278082870, 360581882226366333, 360581880136290022, 360581878046225762, 360581875457441969, 360581873547860691, 360581871156530339, 360581868765264712, 360581867335315637]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 32180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 32100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360506963502978367, 360506969776667167⟩, ⟨2411236009477221351, 2411372609933300661⟩, true⟩

def words09 : List Nat := [360581867300346999, 360581867763587809, 360581867763980091, 360581867472695563, 360581866217894863, 360581864526328778, 360581862834744727, 360581861294151585, 360581859450115556, 360581857124801742]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 32190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 32100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 32100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk321
