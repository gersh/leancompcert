import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk878

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494074586079203, 362494191012317755⟩, ⟨(-797932588645231149), (-791030567811460043)⟩, true⟩

def state01 : KState := ⟨⟨362491374318658465, 362491490772536436⟩, ⟨(-560861503905077190), (-553957056193069616)⟩, true⟩

def words00 : List Nat := [371285181729236813, 371285181732330199, 371285181851375219, 371285181978332458, 371285182115164882, 371285182118224017, 371285182104061977, 371285182091057745, 371285182181686347, 371285182257017959]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 87800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 87800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362488077615358358, 362488194096704779⟩, ⟨(-271319414914376214), (-264412555053581292)⟩, true⟩

def words01 : List Nat := [371285182460529454, 371285182665256987, 371285182844035067, 371285182894188078, 371285182947895436, 371285183003094220, 371285183173209018, 371285183210050863, 371285183246621584, 371285183284313056]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 87810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 87800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362494585635225845, 362494702144000655⟩, ⟨(-842827743898472480), (-835918475139923614)⟩, true⟩

def words02 : List Nat := [371285183432614406, 371285183542919040, 371285183761637808, 371285183981658566, 371285184180738928, 371285184207746998, 371285184347119732, 371285184488060072, 371285184681251441, 371285184792779106]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 87820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 87800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362492986992239275, 362493103528935749⟩, ⟨(-702382753597669933), (-695471032341514199)⟩, true⟩

def words03 : List Nat := [371285184902051191, 371285185012358065, 371285185250911903, 371285185426008659, 371285185605344634, 371285185785864037, 371285185946374226, 371285185957523759, 371285186049739874, 371285186143747267]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 87830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 87800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362485163916588396, 362485280480550341⟩, ⟨(-15182813462780298), (-8268697066029086)⟩, true⟩

def words04 : List Nat := [371285186291961363, 371285186295020656, 371285186284164083, 371285186244979725, 371285186204651507, 371285186205254797, 371285186225809798, 371285186296271730, 371285186354420575, 371285186358718307]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 87840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 87800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk878
