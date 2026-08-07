import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk146

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360636792241399449, 360636793443498829⟩, ⟨(-837760729527618637), (-837748845036058263)⟩, true⟩

def state01 : KState := ⟨⟨360563939234248956, 360563940438084764⟩, ⟨225995601469706629, 226007511321727323⟩, true⟩

def words00 : List Nat := [360579418454843720, 360579420168329385, 360579423364401129, 360579426560087729, 360579427011725185, 360579427011907451, 360579424608573878, 360579419725733080, 360579414843527473, 360579409809154013]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 14600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 14600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360375950920618289, 360375952126172142⟩, ⟨2973748804499888951, 2973760739461115611⟩, true⟩

def words01 : List Nat := [360579409651416302, 360579410552338715, 360579410552501258, 360579409087666650, 360579402980629113, 360579394340613696, 360579385701722257, 360579379994527340, 360579369646980337, 360579355733522424]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 14610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 14600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360579200900071404, 360579202107350346⟩, ⟨895072210757956, 907032401168564⟩, true⟩

def words02 : List Nat := [360579341821926365, 360579332560912366, 360579325638973716, 360579318569993254, 360579311501967733, 360579300435389102, 360579286705808039, 360579277623051085, 360579268541482630, 360579264105463892]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 14620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 14600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360614895964039425, 360614897173055740⟩, ⟨(-521554737551540740), (-521542751934707786)⟩, true⟩

def words03 : List Nat := [360579264101389174, 360579261736747206, 360579261650098847, 360579266364142494, 360579269910500779, 360579273456404163, 360579273456570209, 360579272438819494, 360579272667934248, 360579275101343787]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 14630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 14600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360539992562386387, 360539993773122431⟩, ⟨575137008933860252, 575149019736374518⟩, true⟩

def words04 : List Nat := [360579278279427096, 360579278279609821, 360579276834278903, 360579273084227777, 360579269334656230, 360579263043791079, 360579259078647034, 360579258049904258, 360579257021282470, 360579253091875768]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 14640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 14600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360656878071874735, 360656879284340062⟩, ⟨(-1138357487676315185), (-1138345451531334461)⟩, true⟩

def words05 : List Nat := [360579250412393243, 360579244893041151, 360579239374386137, 360579238486431478, 360579236230083401, 360579229989621111, 360579223749975647, 360579224228983093, 360579229526201924, 360579234822739126]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 14650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 14600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360511431527051808, 360511432741260816⟩, ⟨993801184245366261, 993813245961265119⟩, true⟩

def words06 : List Nat := [360579237748247447, 360579237748430422, 360579236063179550, 360579233019326636, 360579229975842442, 360579223620019027, 360579212655944146, 360579199341286970, 360579186028410029, 360579177338804188]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 14660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 14600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360433465713106345, 360433466929043121⟩, ⟨2138264647119839757, 2138276734190740297⟩, true⟩

def words07 : List Nat := [360579172721367378, 360579169588261888, 360579166455560597, 360579160447467145, 360579156571966325, 360579151353346069, 360579146135384484, 360579142265577181, 360579136029895315, 360579126107121510]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 14670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 14600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360616761368300696, 360616762585968281⟩, ⟨(-553414738247871827), (-553402625760051233)⟩, true⟩

def words08 : List Nat := [360579116185658515, 360579109247538269, 360579104621890921, 360579104608786810, 360579104595671336, 360579099986971287, 360579095543792314, 360579093041557997, 360579090539608748, 360579093085882511]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 14680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 14600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360548401283813260, 360548402503229885⟩, ⟨451032362614100832, 451044500804014468⟩, true⟩

def words09 : List Nat := [360579093086046108, 360579092786536139, 360579092487034632, 360579094365235397, 360579095521141705, 360579096676921726, 360579096677087071, 360579094578326463, 360579087889832953, 360579085802604308]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 14690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 14600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 14600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk146
