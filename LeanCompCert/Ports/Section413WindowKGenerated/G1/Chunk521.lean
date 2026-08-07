import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk521

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504330923023183, 362504370275247956⟩, ⟨(-1008412701494187713), (-1007027611064329103)⟩, true⟩

def state01 : KState := ⟨⟨362481206075460035, 362481245443456307⟩, ⟨196448191192473430, 197834103397712480⟩, true⟩

def words00 : List Nat := [371285042199962719, 371285042201707273, 371285042277596382, 371285042501055253, 371285042751963390, 371285042753707939, 371285042514010173, 371285042203718915, 371285041912438487, 371285041914448396]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 52100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 52100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362464964441630596, 362465003825340585⟩, ⟨1042925091835493631, 1044311822963399853⟩, true⟩

def words01 : List Nat := [371285042005590945, 371285042170310493, 371285042299784951, 371285042301529954, 371285041991097006, 371285041697490056, 371285041403018094, 371285041270960655, 371285040888983483, 371285040506517934]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 52110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 52100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482663443897967, 362482702843263086⟩, ⟨120474038135431143, 121861585286800473⟩, true⟩

def words02 : List Nat := [371285040123276251, 371285040108618289, 371285040186373582, 371285040383947830, 371285040523772274, 371285040525518073, 371285040298702216, 371285040370698893, 371285040489352615, 371285040491168070]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 52120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 52100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362482494976147231, 362482534391389443⟩, ⟨129297153971508833, 130685528876067275⟩, true⟩

def words03 : List Nat := [371285040447631973, 371285040404813505, 371285040597023880, 371285040651035298, 371285040817350588, 371285040984379973, 371285041150156231, 371285041151902262, 371285040872458087, 371285040826542418]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 52130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 52100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483009105993901, 362483048536804419⟩, ⟨102494289619033425, 103883476336918263⟩, true⟩

def words04 : List Nat := [371285040991922697, 371285040993671780, 371285040866909902, 371285040688386246, 371285040509179288, 371285040443745714, 371285040311023672, 371285040429644890, 371285040547932348, 371285040549773488]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 52140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 52100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362500078666520130, 362500118113126271⟩, ⟨(-787766227420016833), (-786376216883030525)⟩, true⟩

def words05 : List Nat := [371285040656397097, 371285040802124392, 371285041314236661, 371285041387495284, 371285041408130708, 371285041429290893, 371285041600921074, 371285041602845450, 371285041879987320, 371285042171007006]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 52150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 52100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362491322046845901, 362491361509209639⟩, ⟨(-330997089202534906), (-329606256670122360)⟩, true⟩

def words06 : List Nat := [371285042461569542, 371285042463328048, 371285042752833605, 371285043082698815, 371285043524632483, 371285043526379295, 371285043478852738, 371285043432207851, 371285043580118338, 371285043703212627]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 52160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 52100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362479940034553992, 362479979512647156⟩, ⟨262855172098497788, 264246825317066432⟩, true⟩

def words07 : List Nat := [371285043904313920, 371285044106079639, 371285044218556950, 371285044220307974, 371285043952302854, 371285043794210945, 371285043841975666, 371285043843753305, 371285043747756839, 371285043652649400]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 52170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 52100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362506975796771076, 362507015290496487⟩, ⟨(-1147948715784992767), (-1146556246795154275)⟩, true⟩

def words08 : List Nat := [371285043826666564, 371285043962513533, 371285044464501335, 371285044967207894, 371285045378951530, 371285045380699155, 371285045576337323, 371285045805709733, 371285046401026041, 371285046823772433]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 52180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 52100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487421369439410, 362487460879144533⟩, ⟨(-127252103162261086), (-125858800114001054)⟩, true⟩

def words09 : List Nat := [371285047245622627, 371285047668089982, 371285048252084390, 371285048653495136, 371285049055733133, 371285049458593798, 371285049844265305, 371285049846013354, 371285049788815109, 371285049837208287]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 52190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 52100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 52100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk521
