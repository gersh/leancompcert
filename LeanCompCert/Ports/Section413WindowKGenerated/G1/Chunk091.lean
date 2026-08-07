import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk091

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362358699871334619, 362358700904513448⟩, ⟨1122355455225534764, 1122361821377079952⟩, true⟩

def state01 : KState := ⟨⟨362452491128427016, 362452492163970581⟩, ⟨268717783013345988, 268724170696017128⟩, true⟩

def words00 : List Nat := [371282023816612800, 371282019067449877, 371282011218753930, 371282013303020591, 371282013330123261, 371282013330387918, 371282000757808514, 371281993128301049, 371281989877275054, 371281989877548629]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 9100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 9100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362456506739123269, 362456507777080151⟩, ⟨232363654486341072, 232370064166271680⟩, true⟩

def words01 : List Nat := [371281986640153345, 371281983416976056, 371281984854912878, 371281985586146191, 371281989964309136, 371281994341610008, 371281998610498189, 371281998610763010, 371281989744526865, 371281986950782594]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 9110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 9100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362401961831853135, 362401962872172615⟩, ⟨729902937390858507, 729909368629950307⟩, true⟩

def words02 : List Nat := [371281986303118768, 371281986303383595, 371281972494426710, 371281958710997216, 371281944930490786, 371281934555473042, 371281919625647743, 371281916646080683, 371281913667071175, 371281909133796926]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 9120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 9100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500579315114594, 362500580357824391⟩, ⟨(-170793632441978407), (-170787179366871201)⟩, true⟩

def words03 : List Nat := [371281900378500440, 371281899833567147, 371281910675439071, 371281910675704247, 371281906146080225, 371281898295322859, 371281894520819405, 371281894521111294, 371281894670509090, 371281896714966184]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 9130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 9100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362391337498301800, 362391338543408353⟩, ⟨828079906685086502, 828086381678811196⟩, true⟩

def words04 : List Nat := [371281896715166197, 371281896430060551, 371281886286675252, 371281884391829767, 371281882497263889, 371281882442742899, 371281870546818917, 371281858654391329, 371281846764461912, 371281839787307677]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 9140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 9100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362413089648350222, 362413090695852893⟩, ⟨629404729866099925, 629411226796302553⟩, true⟩

def words05 : List Nat := [371281831902333264, 371281833906800186, 371281836148249487, 371281836148515560, 371281825928089620, 371281819324670437, 371281818000428510, 371281818000694968, 371281811213818297, 371281803711878691]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 9150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 9100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362439757535170032, 362439758585057555⟩, ⟨385087449471631551, 385093968259305153⟩, true⟩

def words06 : List Nat := [371281800586973272, 371281800587268619, 371281799092491427, 371281796919020932, 371281794745945674, 371281791475962180, 371281772398039281, 371281762888605164, 371281753564958445, 371281753565238505]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 9160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 9100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500474157010506, 362500475209324349⟩, ⟨(-171800879926257074), (-171794338877149264)⟩, true⟩

def words07 : List Nat := [371281748986333851, 371281744330974282, 371281746859417336, 371281749929087944, 371281756336447084, 371281762742513490, 371281766538035072, 371281766538302943, 371281761228724338, 371281763267392409]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 9170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 9100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362450631896316573, 362450632951005222⟩, ⟨286184158496480045, 286190721358832949⟩, true⟩

def words08 : List Nat := [371281777120290939, 371281777120557685, 371281775219567294, 371281773334153805, 371281771449042250, 371281769715450709, 371281766233046887, 371281770392752268, 371281774487329644, 371281774487605748]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 9180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 9100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362525011887730942, 362525012944841185⟩, ⟨(-398108191152927996), (-398101606024152582)⟩, true⟩

def words09 : List Nat := [371281771099527202, 371281769773438139, 371281775734948687, 371281775735215780, 371281767310020187, 371281756934596737, 371281746561322389, 371281743396094198, 371281741030839336, 371281745734100597]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 9190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 9100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 9100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk091
