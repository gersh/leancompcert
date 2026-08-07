import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk219

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362510234690627748, 362510241162372833⟩, ⟨(-573217573705358510), (-573121728885464110)⟩, true⟩

def state01 : KState := ⟨⟨362466009380730670, 362466015858577858⟩, ⟨395514906434643971, 395610884922464821⟩, true⟩

def words00 : List Nat := [371284074641365509, 371284074642049958, 371284074506564800, 371284073877237768, 371284073247700441, 371284072949405879, 371284071796375161, 371284071984224152, 371284072036995863, 371284072037716264]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 21900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 21900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362500430527710910, 362500437011749218⟩, ⟨(-358750131187856779), (-358654017021464193)⟩, true⟩

def words01 : List Nat := [371284072470214859, 371284073727032075, 371284076281005090, 371284076281689682, 371284076063343067, 371284075520649492, 371284075021054226, 371284075021811661, 371284075057639881, 371284075804823373]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 21910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 21900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362473092297628168, 362473098787844093⟩, ⟨240438157006271334, 240534406616856670⟩, true⟩

def words02 : List Nat := [371284076548159535, 371284076548844512, 371284074874115122, 371284074247446096, 371284073620482623, 371284073602778388, 371284071452119951, 371284069298898746, 371284067145590681, 371284067069039573]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 21920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 21900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362454660209906579, 362454666706291920⟩, ⟨644778181946264751, 644874566884428641⟩, true⟩

def words03 : List Nat := [371284066569388656, 371284066537191005, 371284066504776904, 371284066479432584, 371284064615003949, 371284063023999024, 371284061916647470, 371284061917344831, 371284060687337077, 371284059348355933]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 21930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 21900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480898504044193, 362480905006565685⟩, ⟨69145087871976098, 69241607468026522⟩, true⟩

def words04 : List Nat := [371284058215212550, 371284058215975728, 371284059101001798, 371284060581193394, 371284061453561342, 371284061454247267, 371284059562088673, 371284058965433670, 371284059521001591, 371284059521712293]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 21940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 21900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362462068913948450, 362462075422741443⟩, ⟨482701784125102518, 482798441411453226⟩, true⟩

def words05 : List Nat := [371284059378523753, 371284059223021205, 371284060438566286, 371284060777850726, 371284061748725029, 371284062719771156, 371284063630166886, 371284063630853188, 371284061780156322, 371284060779818468]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 21950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 21900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362445296299365800, 362445302814274486⟩, ⟨851207037742829132, 851303829361704662⟩, true⟩

def words06 : List Nat := [371284060848676182, 371284060849362662, 371284059485560567, 371284058116813336, 371284056747932581, 371284055631905964, 371284053759449948, 371284052930108093, 371284052100607044, 371284051281701055]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 21960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 21900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497736922997441, 362497743444111278⟩, ⟨(-301249208667510277), (-301152280690092201)⟩, true⟩

def words07 : List Nat := [371284049540197550, 371284049562657094, 371284050152073774, 371284050152760581, 371284047985343682, 371284045538817440, 371284043092229536, 371284042713584317, 371284042247670174, 371284042871767432]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 21970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 21900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362416821067394041, 362416827594702489⟩, ⟨1477600045033255223, 1477697109200414861⟩, true⟩

def words08 : List Nat := [371284043236194311, 371284043236881926, 371284041392483358, 371284040389768490, 371284039386797408, 371284039014898758, 371284035888947868, 371284032308143090, 371284028727394124, 371284026189936706]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 21980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 21900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362434766497377536, 362434773030884339⟩, ⟨1083081784492947394, 1083178984993036348⟩, true⟩

def words09 : List Nat := [371284023134672035, 371284022144646881, 371284021154474865, 371284020160027934, 371284017459940619, 371284015255283251, 371284013050468100, 371284012909935360, 371284010676581401, 371284008439293114]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 21990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 21900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 21900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk219
