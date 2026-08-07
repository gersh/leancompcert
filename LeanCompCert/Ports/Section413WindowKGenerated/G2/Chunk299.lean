import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk299

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360609879052525428, 360609884428035494⟩, ⟨(-790386187739549969), (-790277489220766695)⟩, true⟩

def state01 : KState := ⟨⟨360565650499787119, 360565655879070029⟩, ⟨532009051651563343, 532117862997576673⟩, true⟩

def words00 : List Nat := [360583454955535567, 360583454955932021, 360583454170973515, 360583453763583372, 360583453356108411, 360583452667473499, 360583451515415156, 360583449790723308, 360583448066073300, 360583446513071954]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 29900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 29900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360511264518249087, 360511269901272324⟩, ⟨2158879019112952858, 2158987942351197088⟩, true⟩

def words01 : List Nat := [360583445918612694, 360583445300619889, 360583444682627013, 360583443277233995, 360583440758939755, 360583437754071677, 360583434749284306, 360583432857551894, 360583431000572415, 360583428589185132]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 29910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 29900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360618685089816550, 360618690476581249⟩, ⟨(-1055731955238488410), (-1055622920037373786)⟩, true⟩

def words02 : List Nat := [360583426177865887, 360583424879316470, 360583424143484330, 360583423921329377, 360583423699169236, 360583422496408791, 360583420980108539, 360583420576075959, 360583420749473690, 360583421928252180]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 29920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 29900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360545839388802792, 360545844779350467⟩, ⟨1125068738118931056, 1125177886563488206⟩, true⟩

def words03 : List Nat := [360583422244916641, 360583422561607619, 360583423499613705, 360583424994041450, 360583426207633666, 360583427421209414, 360583427828895389, 360583427829292292, 360583427125889300, 360583425871086055]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 29930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 29900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583131202947951, 360583136597233006⟩, ⟨8359072981316691, 8468333341289815⟩, true⟩

def words04 : List Nat := [360583424616235717, 360583424158307270, 360583423548148370, 360583422386268453, 360583421224400846, 360583419608850155, 360583419282318754, 360583419674585264, 360583419674939150, 360583419346259427]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 29940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 29900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360616746881240613, 360616752279279595⟩, ⟨(-998772092913250619), (-998662720104147069)⟩, true⟩

def words05 : List Nat := [360583420096112096, 360583420855476425, 360583421015183816, 360583421015582018, 360583420823981723, 360583419671517793, 360583418519055313, 360583417964307204, 360583419077255963, 360583420190227022]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 29950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 29900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360556469147957438, 360556474549781994⟩, ⟨807204435479314733, 807313921722567213⟩, true⟩

def words06 : List Nat := [360583420732989595, 360583420733386909, 360583420701464388, 360583420851440915, 360583420851775079, 360583420383277394, 360583418806289376, 360583416349981955, 360583413893763114, 360583411951240872]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 29960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 29900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360500119422133890, 360500124827700236⟩, ⟨2496275764522251934, 2496385362925960834⟩, true⟩

def words07 : List Nat := [360583411052781345, 360583409929678388, 360583408806607127, 360583406965056797, 360583405156022782, 360583402610869435, 360583400065770117, 360583398171448958, 360583395962514493, 360583393185369548]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 29970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 29900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360601546780715446, 360601552190039886⟩, ⟨(-545132890865428726), (-545023179775689826)⟩, true⟩

def words08 : List Nat := [360583390408325807, 360583387607893191, 360583385499969315, 360583384500376464, 360583383500819322, 360583381544118231, 360583379937258448, 360583379153230500, 360583378692470227, 360583379298846672]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 29980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 29900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572590979021267, 360572596392130351⟩, ⟨323398018541461850, 323507843151647332⟩, true⟩

def words09 : List Nat := [360583379299202714, 360583379197000241, 360583379780400577, 360583381025711749, 360583381492415612, 360583381959147443, 360583381959507875, 360583381517154267, 360583380345913502, 360583379986902073]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 29990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 29900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 29900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk299
