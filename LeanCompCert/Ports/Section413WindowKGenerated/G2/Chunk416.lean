import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk416

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588207140395817, 360588217834117022⟩, ⟨(-242312518876216977), (-242011869092180335)⟩, true⟩

def state01 : KState := ⟨⟨360599522589347047, 360599533288458807⟩, ⟨(-713241158552770679), (-712940284495915893)⟩, true⟩

def words00 : List Nat := [360582400381465329, 360582400086314387, 360582400359158796, 360582400784124403, 360582400959071502, 360582400959637108, 360582400736700597, 360582400105570127, 360582399474352132, 360582399831332184]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 41600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 41600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360543686334185856, 360543697038622363⟩, ⟨1610485255947740912, 1610786351594265296⟩, true⟩

def words01 : List Nat := [360582400819721060, 360582401808170719, 360582402280257742, 360582402280823432, 360582402178522384, 360582401536226931, 360582400893789269, 360582400827504017, 360582400186877297, 360582399257545820]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 41610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 41600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360604230632394994, 360604241342180941⟩, ⟨(-909554751806498391), (-909253433490162493)⟩, true⟩

def words02 : List Nat := [360582398328131044, 360582398072056719, 360582398617744144, 360582399163517582, 360582399167972654, 360582399168541191, 360582399417728348, 360582399830572506, 360582400038844198, 360582400564071116]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 41620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 41600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360563959042687533, 360563969757861695⟩, ⟨767162413574249732, 767463956228876614⟩, true⟩

def words03 : List Nat := [360582400800584937, 360582401037149109, 360582401219816550, 360582401706721054, 360582401813575318, 360582401920523300, 360582401921027701, 360582401739486932, 360582401130597759, 360582400688606865]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 41630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 41600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360599745912423913, 360599756632936870⟩, ⟨(-723295608897298652), (-722993843909290894)⟩, true⟩

def words04 : List Nat := [360582400379242351, 360582400379808669, 360582400135819408, 360582399454349523, 360582398772819653, 360582397944951473, 360582397746931150, 360582397935872286, 360582397936376788, 360582398253932542]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 41640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 41600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360624857143502942, 360624867869357332⟩, ⟨(-1769314231369675176), (-1769012243884343292)⟩, true⟩

def words05 : List Nat := [360582399246259883, 360582400238714153, 360582401498849900, 360582402397425862, 360582402807600014, 360582403217798855, 360582403316058470, 360582403761064147, 360582404780823858, 360582405800662766]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 41650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 41600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360611145706020184, 360611156437275040⟩, ⟨(-1198222767645446093), (-1197920555150321023)⟩, true⟩

def words06 : List Nat := [360582406527492908, 360582406942395811, 360582407761733166, 360582408581208166, 360582409083110843, 360582409175684218, 360582409176191615, 360582408807155490, 360582408643123089, 360582409333650210]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 41660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 41600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360583232798304125, 360583243534900881⟩, ⟨(-34992447080958186), (-34690011962164832)⟩, true⟩

def words07 : List Nat := [360582410010613101, 360582410687643981, 360582411014355452, 360582411014922197, 360582410960290210, 360582410760669419, 360582410756802874, 360582411219879163, 360582411240361345, 360582411260916040]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 41670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 41600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360659546852228516, 360659557594172748⟩, ⟨(-3216160664531131675), (-3215858006502633037)⟩, true⟩

def words08 : List Nat := [360582411855676114, 360582412737868458, 360582414033985358, 360582415330149961, 360582416081513055, 360582416583498192, 360582417659504247, 360582418735631032, 360582420198367395, 360582422049174964]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 41680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 41600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360614163712422191, 360614174459767779⟩, ⟨(-1323772880863829251), (-1323469997626124205)⟩, true⟩

def words09 : List Nat := [360582423538724629, 360582425028272038, 360582426968555740, 360582429195868616, 360582431169267358, 360582433142663509, 360582434761229006, 360582435807903020, 360582436569489288, 360582437331218677]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 41690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 41600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 41600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk416
