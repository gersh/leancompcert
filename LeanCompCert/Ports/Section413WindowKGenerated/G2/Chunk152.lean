import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk152

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360610417465081291, 360610418772908941⟩, ⟨(-453188985172412418), (-453175525103352514)⟩, true⟩

def state01 : KState := ⟨⟨360567696067280537, 360567697376922373⟩, ⟨195993777943767862, 196007265597206156⟩, true⟩

def words00 : List Nat := [360580606555127254, 360580606241759760, 360580606426996012, 360580607500510669, 360580607500670089, 360580607472181734, 360580603145020289, 360580595901564947, 360580588659025941, 360580584113648028]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 15200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 15200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360410636809113047, 360410638120550675⟩, ⟨2585405651033958691, 2585419166010585175⟩, true⟩

def words01 : List Nat := [360580583266606461, 360580580622822418, 360580577979366356, 360580572064979031, 360580561856065703, 360580548981695007, 360580536108961093, 360580527536893811, 360580519135269804, 360580507973770819]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 15210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 15200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360545450791279222, 360545452104516430⟩, ⟨532826582207793441, 532840124582771523⟩, true⟩

def words02 : List Nat := [360580496813695817, 360580488151359933, 360580482379997927, 360580477809546786, 360580473239683154, 360580464511858136, 360580454063349966, 360580447909055901, 360580441755512557, 360580438324121340]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 15220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 15200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360503914335167792, 360503915650223498⟩, ⟨1165829403477351728, 1165842973557240820⟩, true⟩

def words03 : List Nat := [360580436027251098, 360580431564899122, 360580427103093058, 360580428943885482, 360580428944046315, 360580428105179890, 360580427266403486, 360580424266779844, 360580419552726815, 360580414533002845]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 15230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 15200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360529333464597140, 360529334781450945⟩, ⟨778262598972659696, 778276196464412632⟩, true⟩

def words04 : List Nat := [360580409513874988, 360580408780924427, 360580403771524119, 360580396599656849, 360580389428699358, 360580381158351128, 360580376895532235, 360580375553206917, 360580374211038376, 360580369286137136]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 15240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 15200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360562240078665905, 360562241397324413⟩, ⟨276088814170853415, 276102439193276883⟩, true⟩

def words05 : List Nat := [360580365939986373, 360580365383395450, 360580364826824444, 360580364129491575, 360580361406532411, 360580355148605381, 360580348891463746, 360580341256321186, 360580335796441420, 360580334610901955]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 15250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 15200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595116804131261, 360595118124609582⟩, ⟨(-226242520555241452), (-226228867753211280)⟩, true⟩

def words06 : List Nat := [360580333425487242, 360580330086078127, 360580325664006233, 360580325514050866, 360580325364063111, 360580323039848198, 360580319422899937, 360580312482724508, 360580305543420547, 360580303844748852]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 15260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 15200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360540327723032752, 360540329045312171⟩, ⟨611119595256980722, 611133275570922648⟩, true⟩

def words07 : List Nat := [360580309083880714, 360580314322363192, 360580317415032301, 360580320662918935, 360580321251613690, 360580321840281161, 360580326694972288, 360580327295847168, 360580327296018805, 360580324678530164]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 15270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 15200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360584609657172084, 360584610981262056⟩, ⟨(-66322629694741407), (-66308921706698871)⟩, true⟩

def words08 : List Nat := [360580322061343919, 360580317665192275, 360580315411889799, 360580312125412676, 360580308839350627, 360580301905160792, 360580290721955039, 360580283803107989, 360580276885105882, 360580274513947512]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 15280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 15200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360529851708582261, 360529853034496263⟩, ⟨771174373477847668, 771188109364303824⟩, true⟩

def words09 : List Nat := [360580274514119772, 360580272665056920, 360580271301335760, 360580273950162284, 360580273950326067, 360580272794757773, 360580271639319738, 360580268331882745, 360580260780491748, 360580257486088702]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 15290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 15200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 15200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk152
