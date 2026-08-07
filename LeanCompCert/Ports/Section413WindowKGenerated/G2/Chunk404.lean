import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk404

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360579364853945972, 360579374915539562⟩, ⟨131648680208535743, 131923410798364451⟩, true⟩

def state01 : KState := ⟨⟨360537689266894448, 360537699333708365⟩, ⟨1815328720060953840, 1815603661577766406⟩, true⟩

def words00 : List Nat := [360582640266167028, 360582639823388921, 360582638770610755, 360582637810745678, 360582636850769777, 360582635734673069, 360582634203793713, 360582632366621152, 360582630529435938, 360582628897221797]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360495103141156116, 360495113213136536⟩, ⟨3536413446541219859, 3536688596862259863⟩, true⟩

def words01 : List Nat := [360582627785858043, 360582626453084455, 360582625120318100, 360582623414448736, 360582621667823374, 360582619622921270, 360582617577962098, 360582615710753296, 360582613858227214, 360582611694008933]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360595587443155723, 360595597520309402⟩, ⟨(-525728864614869889), (-525453505165812757)⟩, true⟩

def words02 : List Nat := [360582609529773479, 360582607831093062, 360582606438168675, 360582605656011138, 360582604873861985, 360582603455470534, 360582602205061849, 360582601565383143, 360582600925570128, 360582601217839372]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360574071972318329, 360574082054695250⟩, ⟨344387581118298179, 344663151769369355⟩, true⟩

def words03 : List Nat := [360582601233662631, 360582601249555596, 360582601875691107, 360582602888911320, 360582603745883355, 360582604602906061, 360582605151912749, 360582605152461011, 360582605092517584, 360582604882384899]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360559668395193948, 360559678482735404⟩, ⟨926905668229483917, 927181447759667025⟩, true⟩

def words04 : List Nat := [360582604812613032, 360582604813161438, 360582604525672871, 360582603752777561, 360582602979831114, 360582602051279867, 360582601600341447, 360582601242383433, 360582600884383290, 360582600150170749]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360585569471129077, 360585579563856974⟩, ⟨(-121078463523669944), (-120802474176732748)⟩, true⟩

def words05 : List Nat := [360582599583962636, 360582599282440250, 360582598980779962, 360582598662959247, 360582597887558425, 360582596595843342, 360582595304085288, 360582594298704400, 360582593837272540, 360582593911644307]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360524372740110344, 360524382838059932⟩, ⟨2355150259170000226, 2355426459812263932⟩, true⟩

def words06 : List Nat := [360582593912133087, 360582593680861139, 360582592841353750, 360582592383912178, 360582591926342593, 360582591313478076, 360582590092510559, 360582588337329808, 360582586582135869, 360582584628517364]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360515590465760506, 360515600568876116⟩, ⟨2710772874844298729, 2711049284581620829⟩, true⟩

def words07 : List Nat := [360582583190850258, 360582582362399238, 360582581533934248, 360582580396923507, 360582579380996598, 360582578211484578, 360582577041870903, 360582576077329986, 360582574784182786, 360582573130254121]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360561479663435424, 360561489771737390⟩, ⟨852933868025003789, 853210487732026035⟩, true⟩

def words08 : List Nat := [360582571476286133, 360582569806696669, 360582568527793772, 360582567857736120, 360582567187668289, 360582565999278879, 360582564451779734, 360582563513133401, 360582562574363315, 360582561900355124]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360550841478536326, 360550851592070086⟩, ⟨1283718223943705408, 1283995055511410880⟩, true⟩

def words09 : List Nat := [360582561380437004, 360582560394840481, 360582559409187497, 360582559087013700, 360582559087483525, 360582558608836594, 360582558130153402, 360582557346560117, 360582555955878276, 360582555173687652]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk404
