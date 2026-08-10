import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk373A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360538805720037187, 360538814241243158⟩, ⟨1592825475562354462, 1593040328032508508⟩, true⟩

def state01 : KState := ⟨⟨360596287573017555, 360596296098972468⟩, ⟨(-551763685276610979), (-551548655647307481)⟩, true⟩

def words00 : List Nat := [360581521952652937, 360581520912240764, 360581520232881549, 360581519445779059, 360581518658683735, 360581517253707854, 360581515531092649, 360581514526481447, 360581513521776915, 360581513631184221]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360587754808308896, 360587763339048408⟩, ⟨(-233331056982754482), (-233115848816137376)⟩, true⟩

def words01 : List Nat := [360581513665985881, 360581513700844165, 360581514453182600, 360581515566498103, 360581516254495001, 360581516942537074, 360581517082946830, 360581517083449922, 360581516933094272, 360581517101037205]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580005850380210, 360580014385853598⟩, ⟨55862274030959235, 56077658889416771⟩, true⟩

def words02 : List Nat := [360581517986134857, 360581518155707928, 360581518156165587, 360581517701753920, 360581517247275783, 360581516607223919, 360581516574346424, 360581516821773290, 360581516822221977, 360581516600128697]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360642084290210353, 360642092830440606⟩, ⟨(-2262037898632812494), (-2261822336177505872)⟩, true⟩

def words03 : List Nat := [360581516560302084, 360581516498665425, 360581516778506686, 360581517014274893, 360581517014739674, 360581516634742972, 360581516590856390, 360581517497121152, 360581519119791907, 360581520742489628]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579539655593690, 360579548200617695⟩, ⟨73551252887363160, 73766994364393574⟩, true⟩

def words04 : List Nat := [360581522002138972, 360581522547079247, 360581523631444322, 360581524715898698, 360581525080947979, 360581525081451392, 360581524974709397, 360581524425479623, 360581523876185940, 360581523220547130]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk373A
