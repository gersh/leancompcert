import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk580

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571411312890724, 360571432671983322⟩, ⟨608672065314417176, 609509024186479858⟩, true⟩

def state01 : KState := ⟨⟨360590935953082344, 360590957319830347⟩, ⟨(-523792529188699532), (-522955126265023966)⟩, true⟩

def words00 : List Nat := [360581941267734904, 360581941493808361, 360581941766924704, 360581942040184478, 360581942058786040, 360581942146746956, 360581942235735115, 360581942324956000, 360581942405593317, 360581942561831605]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360581503561648811, 360581524936106208⟩, ⟨23484407671181163, 24322257854854709⟩, true⟩

def words01 : List Nat := [360581942562553264, 360581942544330117, 360581942804097486, 360581943305527575, 360581943671576993, 360581944037760378, 360581944240233611, 360581944241043635, 360581944147127830, 360581944140826216]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577252737479570, 360577274119575048⟩, ⟨270044745981909560, 270883039365084556⟩, true⟩

def words02 : List Nat := [360581944225319343, 360581944226129539, 360581944115679070, 360581943772897417, 360581943430000827, 360581942885404671, 360581942521573590, 360581942454950547, 360581942388242994, 360581942102331641]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360601248961124276, 360601270350864385⟩, ⟨(-1122587509650342961), (-1121748772611192345)⟩, true⟩

def words03 : List Nat := [360581942239120014, 360581942456591178, 360581942907171479, 360581943061706550, 360581943062453907, 360581942960342499, 360581942858085437, 360581942849368583, 360581943183026861, 360581943516857198]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360582152705930499, 360582174103394258⟩, ⟨(-14298544007938093), (-13459358651423859)⟩, true⟩

def words04 : List Nat := [360581943702448944, 360581943703259278, 360581943778217096, 360581943964702990, 360581943965386064, 360581943932151108, 360581943602715980, 360581943051319839, 360581942499787529, 360581942249358128]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360567469214150089, 360567490619257554⟩, ⟨838063412982695157, 838903042094147729⟩, true⟩

def words05 : List Nat := [360581942250024837, 360581942246606212, 360581942243098542, 360581942048018677, 360581941556758592, 360581940894317452, 360581940231660938, 360581939865951809, 360581939765701308, 360581939517674608]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360594653778440767, 360594675191192852⟩, ⟨(-740342695710098639), (-739502622713450217)⟩, true⟩

def words06 : List Nat := [360581939317338619, 360581939514481037, 360581939889168725, 360581940264000029, 360581940364085169, 360581940364895894, 360581940269004082, 360581940369958586, 360581940514570791, 360581940734704873]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577604481718296, 360577625902202003⟩, ⟨249849946731343032, 250690468741657682⟩, true⟩

def words07 : List Nat := [360581940767249012, 360581940799893590, 360581941128965455, 360581941606528880, 360581941902234305, 360581942198060046, 360581942336158206, 360581942336969159, 360581942271538253, 360581942198151412]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360582910229518510, 360582931657635191⟩, ⟨(-58355454169642614), (-57514488798516658)⟩, true⟩

def words08 : List Nat := [360581942317262656, 360581942318073577, 360581942284643968, 360581942071827496, 360581941858882253, 360581941570462120, 360581941602875800, 360581941698411063, 360581941699135575, 360581941581912644]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360583366306703961, 360583387742484608⟩, ⟨(-84961465662824329), (-84120055054226781)⟩, true⟩

def words09 : List Nat := [360581941643600172, 360581941705519357, 360581941706186739, 360581941686869848, 360581941493940261, 360581941047528189, 360581940600979617, 360581940137990991, 360581939892144859, 360581939917919554]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk580
