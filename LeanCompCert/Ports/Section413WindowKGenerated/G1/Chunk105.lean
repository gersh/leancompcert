import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk105

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362541115429370034, 362541116823582522⟩, ⟨(-590400963832490203), (-590391052975622683)⟩, true⟩

def state01 : KState := ⟨⟨362462950728582570, 362462952125539248⟩, ⟨231046912000136667, 231056851685311443⟩, true⟩

def words00 : List Nat := [371284908882832054, 371284913023638445, 371284917091072776, 371284921157837778, 371284925648008009, 371284926523201904, 371284929752117024, 371284932980535443, 371284936602069382, 371284936602388469]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 10500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 10500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362621824664030546, 362621826063780686⟩, ⟨(-1439415861855091416), (-1439405892796473918)⟩, true⟩

def words01 : List Nat := [371284938763062434, 371284943014661402, 371284956320266619, 371284962196227936, 371284966720616966, 371284971244240397, 371284981554661127, 371284987400535215, 371285000408222934, 371285013413576668]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 10510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 10500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362518010995175149, 362518012397720815⟩, ⟨(-347269419601458594), (-347259421119923908)⟩, true⟩

def words02 : List Nat := [371285024374839353, 371285024375148219, 371285027855559537, 371285032396754451, 371285039534256623, 371285039534566247, 371285037672316471, 371285033536757065, 371285034294693506, 371285037426576582]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 10520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 10500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362498797294566745, 362498798699889910⟩, ⟨(-144462241662214961), (-144452213919136429)⟩, true⟩

def words03 : List Nat := [371285049583180764, 371285061737598571, 371285073805795125, 371285076413736884, 371285079102775496, 371285081791453885, 371285090978980743, 371285092255253822, 371285093555909297, 371285094856429220]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 10530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 10500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493039027050402, 362493040435148508⟩, ⟨(-83184029695371451), (-83173972690205057)⟩, true⟩

def words04 : List Nat := [371285103710035694, 371285109308200644, 371285120688752910, 371285132067274588, 371285141784881479, 371285141785191128, 371285144965062935, 371285150390751101, 371285156645947224, 371285157393475662]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 10540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 10500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362501829421221802, 362501830832147115⟩, ⟨(-175831019808195779), (-175820932961961573)⟩, true⟩

def words05 : List Nat := [371285158068602098, 371285158743706955, 371285166655044548, 371285170120206003, 371285176258615267, 371285182395984121, 371285186936929968, 371285186937239941, 371285181122196634, 371285182699114073]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 10550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 10500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362467894133785918, 362467895547475032⟩, ⟨182630881046233245, 182640997092855019⟩, true⟩

def words06 : List Nat := [371285191221557579, 371285191221867607, 371285187819801275, 371285182740321311, 371285177661687185, 371285175262511645, 371285170549716409, 371285172670067850, 371285174733250178, 371285174733576533]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 10560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 10500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362548151263571352, 362548152680060668⟩, ⟨(-666125172866463591), (-666115027207254869)⟩, true⟩

def words07 : List Nat := [371285175393769732, 371285177688267123, 371285187086912335, 371285187514927633, 371285187515170713, 371285186471106093, 371285188033833533, 371285188034175557, 371285192847275569, 371285198797893836]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 10570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 10500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362543543157991220, 362543544577286580⟩, ⟨(-617524512205010086), (-617514336843869392)⟩, true⟩

def words08 : List Nat := [371285204680987544, 371285205685710209, 371285212952824488, 371285220218737508, 371285229080821233, 371285229081132254, 371285228003059335, 371285226864207239, 371285233496966197, 371285239003040157]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 10580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 10500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362441443158411242, 362441444580514751⟩, ⟨464154951246997718, 464165156360841734⟩, true⟩

def words09 : List Nat := [371285245654483984, 371285252304797543, 371285257105527934, 371285257105839177, 371285250055931585, 371285244388230386, 371285241954868657, 371285241955185330, 371285237877299989, 371285233746209171]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 10590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 10500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 10500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk105
