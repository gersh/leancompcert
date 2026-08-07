import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk407

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362498196628709745, 362498220167481802⟩, ⟨(-530796313082789220), (-530148952632733460)⟩, true⟩

def state01 : KState := ⟨⟨362469349535046547, 362469373085853794⟩, ⟨643324911354837329, 643972761698167095⟩, true⟩

def words00 : List Nat := [371285195035166403, 371285195036502853, 371285194669379397, 371285194585092289, 371285194500146339, 371285194447269722, 371285193590425795, 371285192734723398, 371285191878532420, 371285191625811991]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 40700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 40700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362429546581129161, 362429570144005330⟩, ⟨2263995819104110044, 2264644160833693836⟩, true⟩

def words01 : List Nat := [371285191238168276, 371285191161232745, 371285191083814002, 371285190946320298, 371285190005095868, 371285189118926628, 371285188232100983, 371285187788655585, 371285186541730977, 371285185177424626]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 40710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 40700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362462393185158042, 362462416759989260⟩, ⟨926407644468029339, 927056473069949941⟩, true⟩

def words02 : List Nat := [371285183812574186, 371285182940744730, 371285181857893063, 371285181328235409, 371285180798211169, 371285180183164176, 371285179067122996, 371285178512732750, 371285177957671011, 371285177783143445]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 40720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 40700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362449662657252104, 362449686244270194⟩, ⟨1444981758171269045, 1445631083205229003⟩, true⟩

def words03 : List Nat := [371285177225329990, 371285176667388908, 371285176108963657, 371285175564184771, 371285174778931587, 371285174175725839, 371285173572077581, 371285172902810691, 371285171430829224, 371285170561481909]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 40730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 40700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362432759670422936, 362432783269341912⟩, ⟨2133790751238665072, 2134440561176550578⟩, true⟩

def words04 : List Nat := [371285169691416427, 371285169359361468, 371285168453651982, 371285167548814310, 371285166643488917, 371285165859089881, 371285164773563361, 371285163937487547, 371285163101016537, 371285162178818638]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 40740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 40700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362492010530677563, 362492034141703314⟩, ⟨(-280955914812033625), (-280305611462315105)⟩, true⟩

def words05 : List Nat := [371285160894385979, 371285160212219053, 371285159529360885, 371285159391573554, 371285158841237667, 371285158198870864, 371285157556002352, 371285157425371922, 371285157162478531, 371285157332707894]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 40750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 40700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485917832540068, 362485941455674254⟩, ⟨(-32678224491457464), (-32027427543147660)⟩, true⟩

def words06 : List Nat := [371285157386914305, 371285157388252669, 371285156719313592, 371285156652243150, 371285156661978415, 371285156663329590, 371285156364656339, 371285156042305868, 371285155890542983, 371285155911352478]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 40760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 40700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362470513936639895, 362470537571794203⟩, ⟨595574343480892012, 596225630552938636⟩, true⟩

def words07 : List Nat := [371285156532478137, 371285157154105107, 371285157774409744, 371285157952210817, 371285158138470559, 371285158325376146, 371285158796908400, 371285158798247245, 371285158469063801, 371285158112023555]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 40770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 40700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362476099427682727, 362476123074839396⟩, ⟨367859707053497464, 368511483643732910⟩, true⟩

def words08 : List Nat := [371285157790909310, 371285157792409717, 371285157816536031, 371285158020776381, 371285158133242031, 371285158134581183, 371285157446462782, 371285157359461827, 371285157431963779, 371285157433349907]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 40780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 40700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468415031900975, 362468438691277284⟩, ⟨681416919763949069, 682069194852610537⟩, true⟩

def words09 : List Nat := [371285157212872070, 371285156992215112, 371285156971712104, 371285156973194536, 371285157031126176, 371285157116119643, 371285157198216968, 371285157199556567, 371285156481569395, 371285156073504064]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 40790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 40700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 40700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk407
