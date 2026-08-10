import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk959A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk959A
