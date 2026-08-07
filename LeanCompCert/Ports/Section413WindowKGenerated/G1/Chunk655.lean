import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk655

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362470061081496526, 362470124422083557⟩, ⟨1004310401764983765, 1007112568517044401⟩, true⟩

def state01 : KState := ⟨⟨362481608528453944, 362481671889017127⟩, ⟨247920911707929957, 250724386999610173⟩, true⟩

def words00 : List Nat := [371285499953265518, 371285499868866051, 371285499666828470, 371285499660329854, 371285499653113580, 371285499574436243, 371285499301396382, 371285499183918578, 371285499155627573, 371285499157937897]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 65500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 65500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487474900856983, 362487538281847337⟩, ⟨(-136440917074199528), (-133636103505902998)⟩, true⟩

def words01 : List Nat := [371285499101201893, 371285499025627696, 371285498963188584, 371285498965648585, 371285498876573428, 371285498859651783, 371285498841981445, 371285498824851554, 371285498655893678, 371285498689907259]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 65510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 65500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362470326455367224, 362470389856199906⟩, ⟨987269939249817882, 990076052993488430⟩, true⟩

def words02 : List Nat := [371285498955269604, 371285498957502035, 371285498925090930, 371285498893396502, 371285498895693220, 371285498898153597, 371285498832908235, 371285498757179155, 371285498680696529, 371285498601095275]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 65520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 65500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500914935243238, 362500978356245436⟩, ⟨(-1017370583196118052), (-1014563147643234692)⟩, true⟩

def words03 : List Nat := [371285498372054506, 371285498313575527, 371285498328957589, 371285498331231202, 371285498249216182, 371285498106307692, 371285498049696571, 371285498055812309, 371285498293523392, 371285498532201811]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 65530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 65500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362484508592552714, 362484572033721458⟩, ⟨57949653485467410, 60758410857716648⟩, true⟩

def words04 : List Nat := [371285498723707274, 371285498725940541, 371285498719465159, 371285498834439917, 371285499019529231, 371285499021773265, 371285498984411625, 371285498947313024, 371285498932929437, 371285498935488929]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 65540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 65500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362476126688899444, 362476190150191414⟩, ⟨607502176599045233, 610312253151360315⟩, true⟩

def words05 : List Nat := [371285499141238829, 371285499362066512, 371285499582075598, 371285499584309445, 371285499528730292, 371285499485049956, 371285499626341961, 371285499628575632, 371285499506438622, 371285499366987500]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481985990101353, 362482049471398884⟩, ⟨223438686938164352, 226250075155678172⟩, true⟩

def words06 : List Nat := [371285499283683477, 371285499286188329, 371285499467982022, 371285499676738432, 371285499860565617, 371285499862799396, 371285499820518671, 371285499907215629, 371285499981136548, 371285499983449451]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362480241427762729, 362480304929379914⟩, ⟨337839368550377767, 340652089232768681⟩, true⟩

def words07 : List Nat := [371285499932508370, 371285499835854331, 371285499807884790, 371285499810369515, 371285499765654250, 371285499766374461, 371285499766278378, 371285499766735451, 371285499456735241, 371285499380267880]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362484115940558840, 362484179462106339⟩, ⟨83750697537015656, 86564725353804264⟩, true⟩

def words08 : List Nat := [371285499455662905, 371285499457912385, 371285499411648254, 371285499313348542, 371285499214174766, 371285499157312241, 371285499083827007, 371285499164864449, 371285499245167728, 371285499247521095]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362497386215954587, 362497449757720192⟩, ⟨(-786729253050610655), (-783913899029264907)⟩, true⟩

def words09 : List Nat := [371285499416997054, 371285499607791304, 371285499878726592, 371285499880961368, 371285499842489724, 371285499767920950, 371285499712015602, 371285499714492080, 371285499848175520, 371285500032883235]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk655
