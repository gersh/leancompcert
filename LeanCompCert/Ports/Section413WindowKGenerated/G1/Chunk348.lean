import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk348

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362476804867927858, 362476821857529660⟩, ⟨281559346778899713, 281958934215810271⟩, true⟩

def state01 : KState := ⟨⟨362461098279554326, 362461115279208608⟩, ⟨828237419847410857, 828637357163393725⟩, true⟩

def words00 : List Nat := [371284924199991177, 371284924201120463, 371284923407960906, 371284922609486768, 371284921810607728, 371284921264908481, 371284920308371818, 371284920178030581, 371284920047304026, 371284919857121949]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 34800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 34800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502202235768492, 362502219245638145⟩, ⟨(-602854733070548144), (-602454440105431644)⟩, true⟩

def words01 : List Nat := [371284919174078521, 371284918830534078, 371284918835944448, 371284918837079458, 371284918440441689, 371284917787067206, 371284917133252803, 371284917109270045, 371284917278840283, 371284917776981145]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 34810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 34800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484842606569689, 362484859626634472⟩, ⟨1625642896415707, 2026290907700933⟩, true⟩

def words02 : List Nat := [371284918273876460, 371284918275007996, 371284918174234081, 371284918460367040, 371284918815971117, 371284918817108737, 371284918439859058, 371284918024088916, 371284917801930727, 371284917803232454]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 34820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 34800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362447532256597571, 362447549286859379⟩, ⟨1301486043244931623, 1301887046470773197⟩, true⟩

def words03 : List Nat := [371284918477243922, 371284919153381558, 371284919743993434, 371284919745123723, 371284919237527771, 371284918983415805, 371284918889390879, 371284918890521293, 371284917954205929, 371284916882911928]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 34830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 34800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362509961982608848, 362509979022997154⟩, ⟨(-873840655346500430), (-873439299263934862)⟩, true⟩

def words04 : List Nat := [371284915811161401, 371284915563734221, 371284915071600926, 371284915238257355, 371284915239133599, 371284915177903831, 371284914865313099, 371284915121807869, 371284916201183053, 371284916921500384]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 34840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 34800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362495858808215912, 362495875858899184⟩, ⟨(-382239996117264132), (-381838281202128728)⟩, true⟩

def words05 : List Nat := [371284917638897018, 371284918356623446, 371284919270787264, 371284919805911956, 371284920593381011, 371284921381247139, 371284922164015635, 371284922165147719, 371284922378394794, 371284922694009992]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 34850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 34800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471203534683673, 362471220595442114⟩, ⟨477409382393171135, 477811448581270885⟩, true⟩

def words06 : List Nat := [371284923722079222, 371284923723210613, 371284923654973326, 371284923584889884, 371284923617255298, 371284923618518834, 371284923415271928, 371284923370393236, 371284923325144401, 371284923246677597]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 34860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 34800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362534820642854030, 362534837713841953⟩, ⟨(-1741184441305387398), (-1740782018363331326)⟩, true⟩

def words07 : List Nat := [371284923283990195, 371284923714825500, 371284924813673201, 371284925379915307, 371284925860905744, 371284926342200620, 371284927645137468, 371284928539548156, 371284929971202409, 371284931403289982]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 34870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 34800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362505345757464459, 362505362838675849⟩, ⟨(-713065033606718191), (-712662254019285963)⟩, true⟩

def words08 : List Nat := [371284932527081605, 371284932672760459, 371284933639933126, 371284934607643165, 371284935827280581, 371284935952327686, 371284936010868672, 371284936069819022, 371284936862778836, 371284937449491840]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 34880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 34800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362473990284966490, 362474007376358391⟩, ⟨381150708783568105, 381553843621334671⟩, true⟩

def words09 : List Nat := [371284938342247139, 371284939235413238, 371284940129729758, 371284940130862558, 371284940061995993, 371284940025573953, 371284940772025810, 371284940773158565, 371284940463253714, 371284940151247255]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 34890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 34800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 34800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk348
