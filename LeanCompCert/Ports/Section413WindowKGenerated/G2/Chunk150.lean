import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk150

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360600558168349367, 360600559440422277⟩, ⟨(-300545956823012663), (-300533036658253685)⟩, true⟩

def state01 : KState := ⟨⟨360618473578823890, 360618474852665076⟩, ⟨(-569661242949113327), (-569648296251278949)⟩, true⟩

def words00 : List Nat := [360580526451381060, 360580526505503731, 360580526505672368, 360580524347909433, 360580522190402263, 360580518908449465, 360580521079181673, 360580523455506118, 360580523600222040, 360580526128645939]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 15000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 15000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360702980709466242, 360702981985079370⟩, ⟨(-1838737233672931967), (-1838724260369416893)⟩, true⟩

def words01 : List Nat := [360580530069545346, 360580534009976010, 360580542362270362, 360580546321748493, 360580546321926380, 360580545839777611, 360580549286409602, 360580555440996756, 360580563592050847, 360580571742061634]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 15010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 15000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360721944968906940, 360721946246314217⟩, ⟨(-2123725189479776674), (-2123712189219379364)⟩, true⟩

def words02 : List Nat := [360580577689182906, 360580585876465168, 360580597201913457, 360580608525908860, 360580618589538117, 360580628029933397, 360580635242859027, 360580642454846624, 360580648029916048, 360580657430585432]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 15020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 15000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360588313347663327, 360588314626840396⟩, ⟨(-114199289513899996), (-114186262644457450)⟩, true⟩

def words03 : List Nat := [360580671232178288, 360580685031970778, 360580696606452252, 360580703799164495, 360580708696639919, 360580713593516820, 360580719095192229, 360580721949925785, 360580722454927365, 360580722959887105]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 15030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 15000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360632241443175244, 360632242724132476⟩, ⟨(-775372669472589491), (-775359615820927745)⟩, true⟩

def words04 : List Nat := [360580724135176437, 360580728115159848, 360580731758217351, 360580735400823789, 360580735400997724, 360580734570535952, 360580729366019107, 360580726577931154, 360580723812583918, 360580727235738288]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 15040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 15000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360555513077850793, 360555514360600441⟩, ⟨380116666112118982, 380129746748543918⟩, true⟩

def words05 : List Nat := [360580727884997118, 360580728534190142, 360580733571653647, 360580741440390953, 360580748190468337, 360580754939679783, 360580758182326851, 360580758182515294, 360580757055568173, 360580755379640849]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 15050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 15000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360563113203401474, 360563114487926818⟩, ⟨265651841985634833, 265664949372878777⟩, true⟩

def words06 : List Nat := [360580756412007371, 360580757772130083, 360580757772298047, 360580756920609292, 360580756069000047, 360580752631420782, 360580751624912322, 360580749558337013, 360580747492015504, 360580743217148642]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 15060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 15000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360641493337940946, 360641494624248232⟩, ⟨(-916243186179212316), (-916230051929193878)⟩, true⟩

def words07 : List Nat := [360580742047591982, 360580740751741704, 360580742537314739, 360580742537503403, 360580741257748158, 360580736052392217, 360580730847690902, 360580732633585879, 360580736663048760, 360580740692020317]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 15070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 15000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360579817939992736, 360579819228095986⟩, ⟨13508649224857556, 13521810567040196⟩, true⟩

def words08 : List Nat := [360580741374386214, 360580741374574980, 360580738395396574, 360580739092209069, 360580739092369823, 360580736687446807, 360580732558879422, 360580725827522494, 360580719097021560, 360580715305668355]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 15080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 15000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360439911815734197, 360439913105619458⟩, ⟨2125826166641072299, 2125839354882652991⟩, true⟩

def words09 : List Nat := [360580719555530183, 360580723864239724, 360580725218512095, 360580725218701035, 360580722220788580, 360580718107828731, 360580713995358332, 360580712419371509, 360580706492726396, 360580697168856720]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 15090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 15000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 15000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk150
