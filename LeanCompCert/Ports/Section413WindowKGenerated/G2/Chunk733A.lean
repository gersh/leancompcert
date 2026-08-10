import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk733A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360559819331707705, 360559854087547823⟩, ⟨1654338613976945162, 1656059363792645188⟩, true⟩

def state01 : KState := ⟨⟨360584095168853031, 360584129934528471⟩, ⟨(-125191204841132532), (-123469734048363686)⟩, true⟩

def words00 : List Nat := [360582446677357349, 360582446456893610, 360582446425612986, 360582446503512129, 360582446504483059, 360582446426380740, 360582446162285233, 360582445953209410, 360582445743833175, 360582445743424157]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 73300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 73300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584953957413179, 360584988733024547⟩, ⟨(-188199544661821167), (-186477345417339017)⟩, true⟩

def words01 : List Nat := [360582445744368721, 360582445623838802, 360582445532057439, 360582445654919255, 360582445655798339, 360582445627407844, 360582445598904674, 360582445477851475, 360582445396513333, 360582445432395569]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 73310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 73300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578402556043436, 360578437341461876⟩, ⟨292102560836141598, 293825479184436024⟩, true⟩

def words02 : List Nat := [360582445438356447, 360582445439398763, 360582445319752923, 360582445106159980, 360582444892417823, 360582444546430661, 360582444352277582, 360582444343985398, 360582444335579980, 360582444234673174]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 73320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 73300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583913990748411, 360583948786022514⟩, ⟨(-112047851395850069), (-110324210284030043)⟩, true⟩

def words03 : List Nat := [360582444311872117, 360582444444046379, 360582444630619228, 360582444712547780, 360582444713509157, 360582444636309318, 360582444558917907, 360582444479276082, 360582444500645008, 360582444522237128]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 73330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 73300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587072687026637, 360587107492236556⟩, ⟨(-343859946078270712), (-342135576225803512)⟩, true⟩

def words04 : List Nat := [360582444523175465, 360582444431185810, 360582444153410002, 360582444010385242, 360582443867088316, 360582443677042420, 360582443584938889, 360582443375201775, 360582443165264232, 360582443130793280]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 73340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 73300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk733A
