import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk489

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362471039218776862, 362471073708784025⟩, ⟨681063907774119526, 682203367128053290⟩, true⟩

def state01 : KState := ⟨⟨362479690385695877, 362479724890235104⟩, ⟨258039275891550993, 259179445937417025⟩, true⟩

def words00 : List Nat := [371285024504131106, 371285024505788871, 371285024257039239, 371285024010360775, 371285023763055303, 371285023645835903, 371285023671699264, 371285023894266971, 371285023998054230, 371285023999741083]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 48900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 48900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362496811021366125, 362496845540642157⟩, ⟨(-579376955156455120), (-578236064257595480)⟩, true⟩

def words01 : List Nat := [371285024124641875, 371285024358739516, 371285024910731214, 371285024979768924, 371285024987262540, 371285024995266259, 371285025218199088, 371285025262040923, 371285025504777361, 371285025748236900]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 48910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 48900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362471034161049117, 362471068695057529⟩, ⟨681656067830239170, 682797679510546208⟩, true⟩

def words02 : List Nat := [371285025958264721, 371285025959894821, 371285025675767817, 371285025477409877, 371285025278257433, 371285025161232945, 371285024615500517, 371285024040156008, 371285023464138331, 371285023276694778]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 48920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 48900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362449378793461133, 362449413342109900⟩, ⟨1741492298972820662, 1742634627083515122⟩, true⟩

def words03 : List Nat := [371285023089014150, 371285023187174138, 371285023282203366, 371285023283834392, 371285022892251334, 371285022630887620, 371285022368696227, 371285022282949929, 371285021640976328, 371285020915201104]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 48930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 48900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362472254865252159, 362472289428506784⟩, ⟨621848694296964265, 622991737292336577⟩, true⟩

def words04 : List Nat := [371285020188746761, 371285019848790541, 371285019301013352, 371285019021762932, 371285018741964617, 371285018425139341, 371285017552177660, 371285017096206978, 371285016639429996, 371285016532435126]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 48940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 48900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492006852667287, 362492041430830273⟩, ⟨(-345141207991332406), (-343997435160993686)⟩, true⟩

def words05 : List Nat := [371285016273692900, 371285015905950458, 371285015584075308, 371285015585872900, 371285015450306868, 371285015444776698, 371285015438711895, 371285015434729517, 371285015337357186, 371285015482929679]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 48950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 48900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362468241083647083, 362468275676311571⟩, ⟨818545444564821652, 819689927466674632⟩, true⟩

def words06 : List Nat := [371285015842880917, 371285015844512185, 371285015649322037, 371285015439860203, 371285015229818142, 371285015031620003, 371285014623742080, 371285014513654501, 371285014403018700, 371285014290309257]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 48960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 48900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482256154694962, 362482290762123260⟩, ⟨132208387079932926, 133353593038254018⟩, true⟩

def words07 : List Nat := [371285013949615435, 371285013886835138, 371285014174036620, 371285014175669040, 371285014050084035, 371285013865975477, 371285013681194096, 371285013659333370, 371285013429061075, 371285013375292682]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 48970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 48900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362467858304053026, 362467892926199382⟩, ⟨837387511529123862, 838533438452889794⟩, true⟩

def words08 : List Nat := [371285013320929131, 371285013226207816, 371285012701555063, 371285012326202312, 371285011950036028, 371285011625610959, 371285010953417693, 371285010279509451, 371285009604979550, 371285009346661781]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 48980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 48900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362459967373056119, 362460002009947485⟩, ⟨1224117006352163216, 1225263655707885744⟩, true⟩

def words09 : List Nat := [371285009064444244, 371285009132288866, 371285009133531003, 371285009115147702, 371285008830389490, 371285008598242278, 371285008408005863, 371285008409638842, 371285007899117145, 371285007390676218]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 48990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 48900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 48900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk489
