import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk878A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk878B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk878A

def state06 : KState := ⟨⟨362500513107837198, 362500629699419824⟩, ⟨(-1363661796655388050), (-1356745253642721974)⟩, true⟩

def words05 : List Nat := [371285186467402353, 371285186577637575, 371285186815778004, 371285186957390751, 371285187077480574, 371285187198577583, 371285187326366560, 371285187391450501, 371285187569285578, 371285187748455885]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 87850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 87800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362492507874910163, 362492624494081183⟩, ⟨(-660328629149719360), (-653409662078385086)⟩, true⟩

def words06 : List Nat := [371285187926550235, 371285187944762577, 371285188060913172, 371285188178739352, 371285188334628158, 371285188337688068, 371285188321157199, 371285188304370823, 371285188395650024, 371285188483769723]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 87860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 87800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362483413947156150, 362483530593954254⟩, ⟨138815200608622196, 145736595412721474⟩, true⟩

def words07 : List Nat := [371285188624295099, 371285188766071331, 371285188891292962, 371285188894354114, 371285188865350141, 371285188854209419, 371285188956065662, 371285188966112647, 371285188968415537, 371285188953028136]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 87870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 87800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362499988881396376, 362500105555568909⟩, ⟨(-1317867106622744383), (-1310943306015982003)⟩, true⟩

def words08 : List Nat := [371285189046746715, 371285189099349506, 371285189243574778, 371285189389012714, 371285189512333607, 371285189515394390, 371285189543568704, 371285189625003397, 371285189824686154, 371285189997593508]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 87880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 87800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362495354317603752, 362495471019641582⟩, ⟨(-910472492459704642), (-903546242632509604)⟩, true⟩

def words09 : List Nat := [371285190169638517, 371285190342745576, 371285190600581018, 371285190810469906, 371285191058732823, 371285191308190795, 371285191554237928, 371285191644913558, 371285191763971418, 371285191884675740]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 87890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 87800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 87800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk878B
