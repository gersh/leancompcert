import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk888

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471461553675792, 362471580751460496⟩, ⟨1197897771912476224, 1205044523349918602⟩, true⟩

def state01 : KState := ⟨⟨362473192736684657, 362473311962063076⟩, ⟨1044190218595922564, 1051339420497831564⟩, true⟩

def words00 : List Nat := [371285150921950897, 371285150898916634, 371285150769600322, 371285150612210531, 371285150453666107, 371285150335181808, 371285150171112694, 371285150134959970, 371285150097765942, 371285150036835037]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 88800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 88800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362502513735945035, 362502632989276691⟩, ⟨(-1559952066805059594), (-1552800382234811852)⟩, true⟩

def words01 : List Nat := [371285149905638834, 371285149902659513, 371285150017993287, 371285150029576485, 371285150031973684, 371285150034055488, 371285150159958900, 371285150233616004, 371285150432548669, 371285150632826811]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 88810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 88800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362484450550352717, 362484569831677612⟩, ⟨44467619296236886, 51621790365124056⟩, true⟩

def words02 : List Nat := [371285150828445533, 371285150870770405, 371285150964837004, 371285151060498497, 371285151138098042, 371285151141198314, 371285151081911555, 371285151014088185, 371285150958185868, 371285150961817938]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 88820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 88800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472628330052232, 362472747639241040⟩, ⟨1094751022147719010, 1101907668511638074⟩, true⟩

def words03 : List Nat := [371285151066492016, 371285151179010961, 371285151290431165, 371285151293527168, 371285151235999464, 371285151211644221, 371285151193166267, 371285151196263668, 371285151058425390, 371285150922317488]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 88830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 88800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480907973192649, 362481027310125016⟩, ⟨359205789057480448, 366364900298727326⟩, true⟩

def words04 : List Nat := [371285150784805134, 371285150762511911, 371285150768241879, 371285150836714743, 371285150884125152, 371285150887224283, 371285150790753360, 371285150737289216, 371285150716035000, 371285150719244867]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 88840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 88800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362487682328701516, 362487801693833399⟩, ⟨(-242733462289775278), (-235571845376025208)⟩, true⟩

def words05 : List Nat := [371285150675191806, 371285150607604621, 371285150594368718, 371285150597782557, 371285150615218859, 371285150637416036, 371285150660341787, 371285150663514485, 371285150645180510, 371285150678816958]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 88850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 88800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362481507073502008, 362481626466203543⟩, ⟨306058504284058893, 313222571184122639⟩, true⟩

def words06 : List Nat := [371285150837227102, 371285150840846429, 371285150843166477, 371285150843138429, 371285150844249919, 371285150847695726, 371285150853837050, 371285150922440829, 371285150965879264, 371285150969086227]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 88860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 88800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362494500834003287, 362494620254778846⟩, ⟨(-848728133382866802), (-841561571408326026)⟩, true⟩

def words07 : List Nat := [371285151010563565, 371285151093403017, 371285151300990625, 371285151362437282, 371285151406495590, 371285151451473220, 371285151570700395, 371285151628032015, 371285151736702051, 371285151846779293]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 88870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 88800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493592204089216, 362493711652784411⟩, ⟨(-767997126254787408), (-760828082639342888)⟩, true⟩

def words08 : List Nat := [371285151951859519, 371285151954964349, 371285152026709679, 371285152128458958, 371285152251515836, 371285152271058596, 371285152289717537, 371285152309452064, 371285152440309966, 371285152540133644]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 88880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 88800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483703390470344, 362483822867080403⟩, ⟨111096033649061559, 118267558755346945⟩, true⟩

def words09 : List Nat := [371285152703317491, 371285152867717459, 371285153000192983, 371285153015580409, 371285153045019198, 371285153076033665, 371285153231785612, 371285153234884147, 371285153222271285, 371285153210823433]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 88890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 88800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 88800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk888
