import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk535A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360538606491160706, 360538624546411730⟩, ⟨2320046833535514290, 2320699496124498116⟩, true⟩

def state01 : KState := ⟨⟨360577850282639701, 360577868344908388⟩, ⟨220274287017135815, 220927325084564131⟩, true⟩

def words00 : List Nat := [360582001296917161, 360582000478412077, 360581999888806230, 360581999648078458, 360581999407302428, 360581998840460546, 360581998068522614, 360581997645517707, 360581997222292768, 360581997055898569]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 53500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 53500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360560109004346232, 360560127073677525⟩, ⟨1169709546214335730, 1170362962237351124⟩, true⟩

def words01 : List Nat := [360581996979403570, 360581996727875854, 360581996476215491, 360581996614738329, 360581996615374741, 360581996448640724, 360581996281829845, 360581995940084133, 360581995249781734, 360581994842030241]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 53510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 53500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360568712484226750, 360568730560560569⟩, ⟨709136524010270432, 709790314844035328⟩, true⟩

def words02 : List Nat := [360581994434051431, 360581993971848483, 360581993518684169, 360581992849683914, 360581992180588252, 360581991422053119, 360581990931026537, 360581990788526057, 360581990645961244, 360581990233918388]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 53520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 53500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360586753941558605, 360586772024903287⟩, ⟨(-256715823067262331), (-256061656907405833)⟩, true⟩

def words03 : List Nat := [360581990024123501, 360581990062253402, 360581990078517282, 360581990153930878, 360581990154616110, 360581989928644317, 360581989702530388, 360581989419137710, 360581989400732907, 360581989490828328]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 53530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 53500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360579960003195915, 360579978093637356⟩, ⟨106867090143732456, 107521636296136432⟩, true⟩

def words04 : List Nat := [360581989491496989, 360581989408998442, 360581989181828559, 360581988946423386, 360581988710829066, 360581988387676479, 360581987862454001, 360581987114699927, 360581986366826499, 360581985967331029]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 53540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 53500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk535A
