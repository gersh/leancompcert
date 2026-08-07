import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk853

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362468247949764812, 362468357595691796⟩, ⟨1438307880870489837, 1444623021517135741⟩, true⟩

def state01 : KState := ⟨⟨362482692508460425, 362482802180951251⟩, ⟨206168190967632240, 212485597646789598⟩, true⟩

def words00 : List Nat := [371285293190737336, 371285293126123923, 371285293031341782, 371285293054852588, 371285293057162653, 371285293038573844, 371285292921858089, 371285292905277492, 371285292924536926, 371285292927612215]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 85300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 85300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362487038006584838, 362487147706145212⟩, ⟨(-164545178956625834), (-158225462844339964)⟩, true⟩

def words01 : List Nat := [371285292900652708, 371285292875067445, 371285292956672592, 371285293003201758, 371285293085307687, 371285293168598197, 371285293250743431, 371285293253710688, 371285293207998964, 371285293233473252]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 85310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 85300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362478113741437908, 362478223467431285⟩, ⟨596916834922649244, 603238806436969186⟩, true⟩

def words02 : List Nat := [371285293361024482, 371285293363990785, 371285293332779704, 371285293258746092, 371285293183607286, 371285293150191348, 371285293047016216, 371285293015833193, 371285292983636175, 371285292948345817]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 85320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 85300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362493555376369446, 362493665129115092⟩, ⟨(-720777365732410156), (-714453111308831768)⟩, true⟩

def words03 : List Nat := [371285292921893564, 371285292979810259, 371285293173430336, 371285293184978512, 371285293187273140, 371285293176894675, 371285293196043145, 371285293199364287, 371285293282454256, 371285293383865929]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 85330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 85300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362478603785730569, 362478713565238686⟩, ⟨555248096974434221, 561574635439964089⟩, true⟩

def words04 : List Nat := [371285293484093012, 371285293487059112, 371285293470607697, 371285293522943299, 371285293590133218, 371285293593099117, 371285293490683490, 371285293381499908, 371285293271145226, 371285293232906407]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 85340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 85300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362468515629789215, 362468625436074796⟩, ⟨1416325931268804338, 1422654755324067488⟩, true⟩

def words05 : List Nat := [371285293157863608, 371285293127365397, 371285293095841696, 371285293054488645, 371285292829318980, 371285292636402667, 371285292441957410, 371285292335423513, 371285292155055404, 371285291963199024]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 85350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 85300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481080590826740, 362481190423596901⟩, ⟨343758947008678834, 350090031928110528⟩, true⟩

def words06 : List Nat := [371285291769962951, 371285291715130619, 371285291613683158, 371285291633714717, 371285291636072142, 371285291623136762, 371285291426362409, 371285291332248855, 371285291276001299, 371285291279072222]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 85360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 85300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362477409955850898, 362477519815668478⟩, ⟨657174295456766873, 663507689547336233⟩, true⟩

def words07 : List Nat := [371285291233279709, 371285291171139899, 371285291153551612, 371285291156866590, 371285291195705515, 371285291239180244, 371285291276556265, 371285291279522910, 371285291133891803, 371285291046513493]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 85370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 85300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481664842554559, 362481774728784343⟩, ⟨293902905694802197, 300238554997841115⟩, true⟩

def words08 : List Nat := [371285291003564073, 371285291006551050, 371285290931695535, 371285290854216501, 371285290775560505, 371285290740138724, 371285290713350844, 371285290762897951, 371285290811378280, 371285290814450087]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 85380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 85300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362481645830743168, 362481755743871170⟩, ⟨295517099513415255, 301855045787768073⟩, true⟩

def words09 : List Nat := [371285290820992483, 371285290870317529, 371285290935573513, 371285290938540882, 371285290821268294, 371285290682837100, 371285290543236049, 371285290496024186, 371285290384245484, 371285290346280863]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 85390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 85300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 85300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk853
