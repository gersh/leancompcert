import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk274

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362451110055948066, 362451120379814259⟩, ⟨939165435561383521, 939356661216896429⟩, true⟩

def state01 : KState := ⟨⟨362472515798485484, 362472526130154300⟩, ⟨352537955514960748, 352729395001854062⟩, true⟩

def words00 : List Nat := [371285402219074264, 371285401434165153, 371285399985614276, 371285399640574870, 371285399295309591, 371285398581086547, 371285396298145120, 371285395345444575, 371285394768252278, 371285394769154733]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 27400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 27400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362459137432962182, 362459147772577167⟩, ⟨719442909730008055, 719634567061993621⟩, true⟩

def words01 : List Nat := [371285394300337470, 371285393828993374, 371285394028425141, 371285394037168329, 371285394446451049, 371285394856045985, 371285395116600762, 371285395117473208, 371285393607134935, 371285392651025818]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 27410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 27400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362440252008947456, 362440262356335533⟩, ⟨1237348702545276442, 1237540573056474602⟩, true⟩

def words02 : List Nat := [371285391694511379, 371285391584197202, 371285389703496617, 371285387564421711, 371285385425158314, 371285383701050267, 371285381494864593, 371285380616448446, 371285379737810971, 371285378673253378]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 27420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 27400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362510600194299628, 362510610549604865⟩, ⟨(-692634484006427591), (-692442396289195377)⟩, true⟩

def words03 : List Nat := [371285377029126268, 371285376712581348, 371285376632093180, 371285376632973231, 371285376032567655, 371285375204188374, 371285374872633467, 371285374873597933, 371285375767389879, 371285376688000361]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 27430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 27400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362459417015441765, 362459427378622947⟩, ⟨711951955958921745, 712144259832760551⟩, true⟩

def words04 : List Nat := [371285377608284226, 371285377609157685, 371285376785803865, 371285376811019668, 371285376896212674, 371285376897086278, 371285375215155706, 371285373269458429, 371285371323540833, 371285370703207019]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 27440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 27400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362456092520303358, 362456102891348582⟩, ⟨803392804437657660, 803585324218403030⟩, true⟩

def words05 : List Nat := [371285369921003392, 371285370084211688, 371285370245436352, 371285370246325826, 371285369523049506, 371285368873419214, 371285368896888222, 371285368897762137, 371285367806222038, 371285366741465786]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 27450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 27400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362458775207840146, 362458785586718125⟩, ⟨729784970998942463, 729977705907022037⟩, true⟩

def words06 : List Nat := [371285365676418416, 371285365165628496, 371285364108569431, 371285364024700380, 371285363940558578, 371285363648679651, 371285361877329168, 371285360701014110, 371285359524318432, 371285359219987402]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 27460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 27400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362478857161716608, 362478867548562784⟩, ⟨178039157971770737, 178232111806873465⟩, true⟩

def words07 : List Nat := [371285358253307690, 371285357285763700, 371285356509790609, 371285356510755860, 371285356192080424, 371285355896493582, 371285355600648491, 371285355225411504, 371285353668212782, 371285353433271914]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 27470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 27400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477859980880413, 362477870375533183⟩, ⟨205653357459944007, 205846525860952037⟩, true⟩

def words08 : List Nat := [371285354283409460, 371285354620925408, 371285354957537687, 371285355294411856, 371285355763599831, 371285355764573247, 371285356718848347, 371285357857086181, 371285358425768590, 371285358426673997]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 27480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 27400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362529450201296027, 362529460603848467⟩, ⟨(-1212830978185311374), (-1212637592582503234)⟩, true⟩

def words09 : List Nat := [371285358906322487, 371285359658740966, 371285361367383739, 371285361502227211, 371285361514926021, 371285361527909977, 371285362636677456, 371285363086268370, 371285364690409068, 371285366294820341]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 27490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 27400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 27400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk274
