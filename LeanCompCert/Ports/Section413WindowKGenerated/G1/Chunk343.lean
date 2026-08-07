import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk343

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362484017452963513, 362484033937931592⟩, ⟨23411349388425265, 23793501338487193⟩, true⟩

def state01 : KState := ⟨⟨362497396697450936, 362497413192362827⟩, ⟨(-435398675841069319), (-435016182766926259)⟩, true⟩

def words00 : List Nat := [371284728436221428, 371284728844072065, 371284730101300044, 371284731358921956, 371284732477916885, 371284732733989203, 371284733078933693, 371284733424415167, 371284734200166101, 371284734570848825]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 34300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 34300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362516329115666190, 362516345620726219⟩, ⟨(-1085011091465055341), (-1084628250159726573)⟩, true⟩

def words01 : List Nat := [371284734938835826, 371284735307185917, 371284736524431402, 371284737520976785, 371284738777062274, 371284740033491375, 371284741237537947, 371284741310449795, 371284742232076476, 371284743154301589]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 34310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 34300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492777386008398, 362492793900975910⟩, ⟨(-276617853811693292), (-276234672428662480)⟩, true⟩

def words02 : List Nat := [371284744421643379, 371284744620667455, 371284744727701664, 371284744835092358, 371284745188036186, 371284745189272755, 371284745895143008, 371284746673255821, 371284747448544801, 371284747684074898]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 34320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 34300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362511711861352636, 362511728386361388⟩, ⟨(-926786984269248397), (-926403458119527619)⟩, true⟩

def words03 : List Nat := [371284748350039124, 371284749016522259, 371284750064925244, 371284750066038069, 371284749984187696, 371284749715944621, 371284750026044709, 371284750212076516, 371284750998452644, 371284751785268831]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 34330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 34300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362504871424255996, 362504887959319049⟩, ⟨(-691836014608848370), (-691452143143523442)⟩, true⟩

def words04 : List Nat := [371284752569425890, 371284752884684467, 371284753895322356, 371284754906500202, 371284756176658410, 371284756643060431, 371284757093653477, 371284757544586406, 371284758346894541, 371284758934162765]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 34340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 34300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362480247875557861, 362480264420654896⟩, ⟨154251372636590218, 154635588820749914⟩, true⟩

def words05 : List Nat := [371284760368279059, 371284761802780924, 371284763050040965, 371284763286228446, 371284763781582287, 371284764277466902, 371284765125509830, 371284765126624010, 371284765004068676, 371284764874345838]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 34350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 34300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362512685593267632, 362512702148346002⟩, ⟨(-960439626651450164), (-960055067458148136)⟩, true⟩

def words06 : List Nat := [371284765460213277, 371284765845712610, 371284766575829893, 371284767306342003, 371284767912076892, 371284767913190823, 371284767714011148, 371284768038739243, 371284769209510688, 371284770023372678]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 34360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 34300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362502025510496691, 362502042075715247⟩, ⟨(-593949177495135715), (-593564269731610271)⟩, true⟩

def words07 : List Nat := [371284770761582026, 371284771500109128, 371284772882649475, 371284773914131660, 371284774983930855, 371284776054097296, 371284776969873589, 371284776970987983, 371284777261371641, 371284777764911850]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 34370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 34300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362494536108693223, 362494552683837478⟩, ⟨(-336399191790477772), (-336013942729519506)⟩, true⟩

def words08 : List Nat := [371284779113769800, 371284779335729078, 371284779547357347, 371284779759384346, 371284780002499873, 371284780003735614, 371284780629018961, 371284781311564993, 371284781995192821, 371284782280454921]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 34380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 34300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362512070680065835, 362512087265316917⟩, ⟨(-939543561397372778), (-939157964712828750)⟩, true⟩

def words09 : List Nat := [371284782717307217, 371284783154704640, 371284784320525303, 371284784578544179, 371284784699076347, 371284784819938131, 371284785206682815, 371284785366004802, 371284786160421887, 371284786955305208]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 34390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 34300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 34300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk343
