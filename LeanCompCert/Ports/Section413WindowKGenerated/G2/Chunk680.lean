import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk680

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360609644582518554, 360609674316013074⟩, ⟨(-1827610280023538349), (-1826244538029301089)⟩, true⟩

def state01 : KState := ⟨⟨360597555601431410, 360597585344071412⟩, ⟨(-1005610919118386040), (-1004244555185416762)⟩, true⟩

def words00 : List Nat := [360582818437707202, 360582818678202446, 360582818982041722, 360582819286160115, 360582819404345104, 360582819405306607, 360582819402112132, 360582819290824415, 360582819212183095, 360582819430392957]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 68000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 68000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360559627744220628, 360559657495927526⟩, ⟨1574118899688411255, 1575485880304936193⟩, true⟩

def words01 : List Nat := [360582819750421191, 360582820070639986, 360582820220290102, 360582820240548282, 360582820241352796, 360582820165862683, 360582820090089951, 360582820087512580, 360582819933077145, 360582819593550357]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 68010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 68000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602854829668166, 360602884590444976⟩, ⟨(-1366365301484597805), (-1364997703886700435)⟩, true⟩

def words02 : List Nat := [360582819253813649, 360582819088206867, 360582819187456696, 360582819345581009, 360582819346468521, 360582819349899320, 360582819527259950, 360582819704897204, 360582819945853118, 360582820241782063]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 68020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 68000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583161092748201, 360583190862702226⟩, ⟨(-26486616839945912), (-25118394872745800)⟩, true⟩

def words03 : List Nat := [360582820429043066, 360582820616395474, 360582820798763909, 360582821174823748, 360582821410097204, 360582821645515331, 360582821772758955, 360582821773720471, 360582821690574668, 360582821697127459]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 68030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 68000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360585257656701256, 360585287435703614⟩, ⟨(-169121579857230105), (-167752742195176821)⟩, true⟩

def words04 : List Nat := [360582821919046923, 360582822079379046, 360582822098585774, 360582822117896480, 360582822118701873, 360582822139948749, 360582822227764613, 360582822315748573, 360582822316613310, 360582822332439957]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 68040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 68000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360612172788973922, 360612202577054969⟩, ⟨(-2000859204485202196), (-1999489748974069604)⟩, true⟩

def words05 : List Nat := [360582822442505444, 360582822552848030, 360582822878549995, 360582823211310297, 360582823355150148, 360582823499056841, 360582823587547722, 360582823804670708, 360582824237108260, 360582824669751608]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 68050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 68000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360590401827161803, 360590431624415527⟩, ⟨(-519162544300890016), (-517792464452114428)⟩, true⟩

def words06 : List Nat := [360582824938850330, 360582824992450503, 360582825162475668, 360582825332777311, 360582825448300298, 360582825449262239, 360582825349274774, 360582825140130763, 360582824930778347, 360582824971590505]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 68060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 68000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360557853963869021, 360557883770174907⟩, ⟨1696642290685176312, 1698012986759544984⟩, true⟩

def words07 : List Nat := [360582825299640414, 360582825627865130, 360582825848027074, 360582825917484485, 360582825918304569, 360582825838331751, 360582825771816698, 360582825772778750, 360582825571888055, 360582825206525665]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 68070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 68000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581498534547601, 360581528349946454⟩, ⟨86821696505376462, 88193011673791164⟩, true⟩

def words08 : List Nat := [360582824840957789, 360582824539342261, 360582824429627658, 360582824458912105, 360582824459810142, 360582824279146279, 360582823959443981, 360582823855447788, 360582823751186125, 360582823591709912]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 68080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 68000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360589111593073345, 360589141417630065⟩, ⟨(-431598591932220696), (-430226653159710550)⟩, true⟩

def words09 : List Nat := [360582823573544943, 360582823447590782, 360582823363406851, 360582823558617908, 360582823699150885, 360582823839855560, 360582823872583340, 360582823873545808, 360582823844531870, 360582823938398340]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 68090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 68000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 68000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk680
