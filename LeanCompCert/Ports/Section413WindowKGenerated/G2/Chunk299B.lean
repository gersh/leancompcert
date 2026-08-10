import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk299A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk299B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk299A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk299B
