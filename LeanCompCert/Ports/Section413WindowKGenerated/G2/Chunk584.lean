import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk584

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360602823333721123, 360602845000377666⟩, ⟨(-1219158065763077887), (-1218303206619864069)⟩, true⟩

def state01 : KState := ⟨⟨360600522057520791, 360600543731962958⟩, ⟨(-1084917798562501576), (-1084062484702773348)⟩, true⟩

def words00 : List Nat := [360581984125860099, 360581984126675631, 360581984083315197, 360581984208845733, 360581984259034803, 360581984332385269, 360581984333111762, 360581984258812295, 360581984195241368, 360581984513926925]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 58400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 58400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360571888685201035, 360571910367309836⟩, ⟨587785567873878708, 588641329581778040⟩, true⟩

def words01 : List Nat := [360581985125505438, 360581985737221507, 360581986201226006, 360581986372930129, 360581986373624536, 360581986347628079, 360581986587639094, 360581986588454817, 360581986563071270, 360581986391438248]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 58410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 58400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580407206289089, 360580428896112411⟩, ⟨90128486427387896, 90984698854026436⟩, true⟩

def words02 : List Nat := [360581986219629767, 360581986042850264, 360581986241281879, 360581986439862879, 360581986440617810, 360581986378709691, 360581986129865018, 360581986152548908, 360581986153221749, 360581986053375017]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 58420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 58400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574203561788240, 360574225259376393⟩, ⟨452624298992986850, 453480965157585526⟩, true⟩

def words03 : List Nat := [360581986027452262, 360581985854098157, 360581985712604953, 360581985891691167, 360581985892378325, 360581985851261944, 360581985810050706, 360581985586399013, 360581985161338690, 360581985029485182]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 58430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 58400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583235070282097, 360583256775569546⟩, ⟨(-75303894172005416), (-74446778022925904)⟩, true⟩

def words04 : List Nat := [360581985057501660, 360581985058317759, 360581984927143875, 360581984519618079, 360581984111971300, 360581983629555590, 360581983353800434, 360581983315825876, 360581983277759596, 360581983114245995]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 58440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 58400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360620107612419314, 360620129325399656⟩, ⟨(-2230660220677679266), (-2229802654839818900)⟩, true⟩

def words05 : List Nat := [360581983429490991, 360581983744964662, 360581984352973457, 360581984919519633, 360581985235105804, 360581985550737216, 360581985855533668, 360581986306483165, 360581986959606657, 360581987612893202]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 58450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 58400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598353949215269, 360598375669970858⟩, ⟨(-959034687285299939), (-958176666867826477)⟩, true⟩

def words06 : List Nat := [360581988081629337, 360581988258598044, 360581988399426458, 360581988540511215, 360581988541198918, 360581988493594286, 360581988476540084, 360581988312276098, 360581988176875228, 360581988458073203]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 58460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 58400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587375929881189, 360587397658334621⟩, ⟨(-317116524551614986), (-316258054002904716)⟩, true⟩

def words07 : List Nat := [360581988730570462, 360581989003203399, 360581989106694820, 360581989146585089, 360581989147269059, 360581989111423379, 360581989331127283, 360581989594822725, 360581989688027182, 360581989781348884]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 58470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 58400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601290752168314, 360601312488326148⟩, ⟨(-1130823760446701037), (-1129964839305972193)⟩, true⟩

def words08 : List Nat := [360581990166999809, 360581990729059925, 360581991522967593, 360581992317004594, 360581992826997235, 360581993045392317, 360581993167403642, 360581993289642796, 360581993546819043, 360581993877953510]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 58480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 58400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582046551053669, 360582068295008612⟩, ⟨(-5102166833887006), (-4242789603456372)⟩, true⟩

def words09 : List Nat := [360581994008936540, 360581994140011591, 360581994427118038, 360581994860217803, 360581995218208760, 360581995576320821, 360581995691910425, 360581995765833014, 360581995767744860, 360581995769930350]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 58490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 58400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 58400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk584
