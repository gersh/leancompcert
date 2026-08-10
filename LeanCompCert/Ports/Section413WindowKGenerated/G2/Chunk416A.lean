import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk416A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk416A
