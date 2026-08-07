import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk959

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360597580182566336, 360597640933965513⟩, ⟨(-1480353391309744633), (-1476419359794717747)⟩, true⟩

def state01 : KState := ⟨⟨360579285510469953, 360579346275104357⟩, ⟨274118632110858877, 278053932950312087⟩, true⟩

def words00 : List Nat := [360582245783281117, 360582245784671690, 360582245812705460, 360582245856848409, 360582245872824915, 360582245874215686, 360582245811019818, 360582245664608121, 360582245517940457, 360582245388157744]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 95900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 95900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586333712874294, 360586394490603526⟩, ⟨(-401845976261384172), (-397909419431618502)⟩, true⟩

def words01 : List Nat := [360582245437583535, 360582245517504574, 360582245543168976, 360582245650761276, 360582245730324113, 360582245810254385, 360582245998516481, 360582246097925151, 360582246142412428, 360582246187109697]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 95910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 95900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595270365541554, 360595331156406203⟩, ⟨(-1259119921973660609), (-1255182105129574819)⟩, true⟩

def words02 : List Nat := [360582246206916941, 360582246285284429, 360582246471958089, 360582246658894701, 360582246752177388, 360582246753568304, 360582246738327555, 360582246723541037, 360582246800695708, 360582246938529505]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 95920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 95900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360578491396500102, 360578552200623383⟩, ⟨350543316260056081, 354482405066694709⟩, true⟩

def words03 : List Nat := [360582246974913380, 360582247011422310, 360582247050386852, 360582247157051566, 360582247189695191, 360582247222545020, 360582247223784168, 360582247202125977, 360582247071849654, 360582247034947614]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 95930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 95900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360594422355837033, 360594483173077378⟩, ⟨(-1177944484029670535), (-1174004136707736177)⟩, true⟩

def words04 : List Nat := [360582247021816787, 360582247111307449, 360582247145864089, 360582247180572340, 360582247181737306, 360582247214957751, 360582247367664339, 360582247520638588, 360582247589175573, 360582247718139882]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 95940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 95900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360605086144545112, 360605146974911644⟩, ⟨(-2201253706153065638), (-2197312099307518120)⟩, true⟩

def words05 : List Nat := [360582247934342501, 360582248150949476, 360582248319210062, 360582248379403943, 360582248380686922, 360582248349334724, 360582248393584494, 360582248525100406, 360582248764849822, 360582249004910211]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 95950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 95900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360588222933243789, 360588283776880864⟩, ⟨(-583087323540505237), (-579144443187784933)⟩, true⟩

def words06 : List Nat := [360582249179341955, 360582249245617831, 360582249308905222, 360582249372590912, 360582249373758373, 360582249374893658, 360582249343781717, 360582249258754049, 360582249173463703, 360582249199319020]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 95960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 95900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360565203888564211, 360565264745297607⟩, ⟨1626238005737838112, 1630182143011056016⟩, true⟩

def words07 : List Nat := [360582249371957456, 360582249544859275, 360582249662883181, 360582249707733865, 360582249708907546, 360582249679679493, 360582249650046625, 360582249617938980, 360582249523266964, 360582249347746149]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 95970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 95900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601370866252863, 360601431736118030⟩, ⟨(-1845275528736484602), (-1841330131011572598)⟩, true⟩

def words08 : List Nat := [360582249171913454, 360582249060877293, 360582249066204514, 360582249107553819, 360582249108850752, 360582249056869030, 360582249026225086, 360582249066173652, 360582249214298561, 360582249415577443]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 95980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 95900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360597736071336592, 360597796954475031⟩, ⟨(-1496366109005376413), (-1492419437111887075)⟩, true⟩

def words09 : List Nat := [360582249533656321, 360582249651869765, 360582249844308430, 360582250092183385, 360582250297470447, 360582250502980540, 360582250627148695, 360582250754014213, 360582250917081820, 360582251080607969]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 95990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 95900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 95900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk959
