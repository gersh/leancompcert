import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk408

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360546993559173856, 360547003829279037⟩, ⟨1447443585337072389, 1447726781564171443⟩, true⟩

def state01 : KState := ⟨⟨360549454951574812, 360549465226902689⟩, ⟨1346965967828205257, 1347249377167051139⟩, true⟩

def words00 : List Nat := [360582486459602684, 360582486189672440, 360582485647909720, 360582484558262656, 360582483468578749, 360582482225600762, 360582481287057181, 360582480303819288, 360582479320569319, 360582477953615923]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360569259182097897, 360569269462648561⟩, ⟨538622569234223756, 538906191741376156⟩, true⟩

def words01 : List Nat := [360582477145146812, 360582476683121290, 360582476357161823, 360582476357715821, 360582475896574766, 360582474919636825, 360582473942649905, 360582472720694261, 360582471799017088, 360582471476165009]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360550187101470133, 360550197387294312⟩, ⟨1316983003931423461, 1317266841729584147⟩, true⟩

def words02 : List Nat := [360582471153249610, 360582470374519691, 360582468998084859, 360582468220480703, 360582467442752548, 360582466292781419, 360582464728456846, 360582462825091123, 360582460921712558, 360582459617069713]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360516518152446397, 360516528443496546⟩, ⟨2691791925775138202, 2692075976976151540⟩, true⟩

def words03 : List Nat := [360582458827386036, 360582457819495683, 360582456811596988, 360582455412007060, 360582453818790625, 360582452072618692, 360582450326369757, 360582448999384722, 360582447686219152, 360582446072707520]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581722023214018, 360581732319496281⟩, ⟨28456448393506434, 28740713299688296⟩, true⟩

def words04 : List Nat := [360582444459149552, 360582443443924111, 360582442732079966, 360582441914177080, 360582441096279868, 360582439713126860, 360582438158370555, 360582437201803106, 360582436245119036, 360582435886529322]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360563831095993075, 360563841397567318⟩, ⟨759495538635947283, 759780019745604447⟩, true⟩

def words05 : List Nat := [360582435869806977, 360582435419289125, 360582435115472316, 360582435718560969, 360582436168604567, 360582436618716543, 360582436768583322, 360582436769138313, 360582436566163620, 360582436111706956]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 40850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 40800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561377900630337, 360561388207425469⟩, ⟨859630392974697513, 859915087435759463⟩, true⟩

def words06 : List Nat := [360582435657083489, 360582435514545338, 360582434775626282, 360582433686616119, 360582432597572011, 360582431118309261, 360582430099480361, 360582429678253837, 360582429256991621, 360582428459136645]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 40860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 40800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585486219878472, 360585496531918195⟩, ⟨(-125933856164408646), (-125648947331076320)⟩, true⟩

def words07 : List Nat := [360582427944789368, 360582427710256713, 360582427475578032, 360582427226254366, 360582426545030363, 360582425372304344, 360582424199526107, 360582423373189621, 360582422926947257, 360582423002715606]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 40870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 40800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360539382718176523, 360539393035498623⟩, ⟨1758840422417454922, 1759125547219980938⟩, true⟩

def words08 : List Nat := [360582423003209963, 360582422779203604, 360582421959309715, 360582421736550187, 360582421513658560, 360582420759517332, 360582419409634815, 360582417472882386, 360582415536117766, 360582413958639244]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 40880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 40800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360565768183656783, 360565778506205505⟩, ⟨679837860292063451, 680123198837662287⟩, true⟩

def words09 : List Nat := [360582412907000351, 360582412297858658, 360582411688686456, 360582410724924181, 360582409995714472, 360582409114311884, 360582408232784151, 360582407947883537, 360582407841282416, 360582407435272441]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 40890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 40800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 40800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk408
