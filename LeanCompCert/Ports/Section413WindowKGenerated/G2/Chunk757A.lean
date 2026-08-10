import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk757A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575494263248518, 360575531426815655⟩, ⟨503154748026154994, 505054890046717104⟩, true⟩

def state01 : KState := ⟨⟨360605386440313601, 360605423614055413⟩, ⟨(-1759866619924419420), (-1757965707632286168)⟩, true⟩

def words00 : List Nat := [360582203134669606, 360582203099533605, 360582203331212159, 360582203563091079, 360582203627160112, 360582203628238528, 360582203581043412, 360582203645351707, 360582203883608061, 360582204191413627]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360586217876283136, 360586255060309811⟩, ⟨(-308493724063997486), (-306592033053599094)⟩, true⟩

def words01 : List Nat := [360582204411751903, 360582204632225938, 360582204879604773, 360582205214750670, 360582205466570246, 360582205718558627, 360582205869754986, 360582205981565314, 360582206035927737, 360582206090630943]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585490444548349, 360585527638731091⟩, ⟨(-253429022037693439), (-251526561958344315)⟩, true⟩

def words02 : List Nat := [360582206319202115, 360582206373806112, 360582206374767602, 360582206322704559, 360582206270465186, 360582206118056123, 360582206189518491, 360582206277457094, 360582206278418278, 360582206322995681]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360592920879149963, 360592958083533859⟩, ⟨(-816177668312208272), (-814274435650744440)⟩, true⟩

def words03 : List Nat := [360582206541905639, 360582206761126327, 360582206933666661, 360582207032451690, 360582207033466573, 360582206943896547, 360582206882014749, 360582207022813318, 360582207165634327, 360582207308713739]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593947125417938, 360593984340066659⟩, ⟨(-894031429858049247), (-892127419687455081)⟩, true⟩

def words04 : List Nat := [360582207364395585, 360582207365474494, 360582207301769481, 360582207357746518, 360582207369369560, 360582207370455836, 360582207363004846, 360582207221252361, 360582207079296161, 360582207235874141]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk757A
