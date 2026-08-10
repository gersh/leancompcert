import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk557A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360574073628161445, 360574093262899587⟩, ⟨429778498818542786, 430517413858254434⟩, true⟩

def state01 : KState := ⟨⟨360559102849638282, 360559122491767371⟩, ⟨1263604230678899395, 1264343557430496429⟩, true⟩

def words00 : List Nat := [360581822342318586, 360581822040450373, 360581821417060681, 360581821016988241, 360581820616722224, 360581820035750383, 360581819569652407, 360581818916828841, 360581818263880915, 360581817583446253]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360539243287706880, 360539262937144554⟩, ⟨2370136782396381291, 2370876516346293089⟩, true⟩

def words01 : List Nat := [360581817176701344, 360581817091523841, 360581817006276987, 360581816669985344, 360581816101696157, 360581815321696422, 360581814541497344, 360581814082833919, 360581813529776311, 360581812766942586]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580802603663849, 360580822260418313⟩, ⟨54327096497452830, 55067238174641828⟩, true⟩

def words02 : List Nat := [360581812003946699, 360581811562526993, 360581811347894575, 360581811361184749, 360581811361900649, 360581811102341987, 360581810968388240, 360581810717696516, 360581810466778171, 360581810368047501]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360589240376735297, 360589260040872073⟩, ⟨(-415966283599542846), (-415225730468834446)⟩, true⟩

def words03 : List Nat := [360581810351011776, 360581810125162132, 360581809993752277, 360581810336128686, 360581810539421819, 360581810742834145, 360581810743536297, 360581810697854713, 360581810708619199, 360581810843145645]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583061972751926, 360583081644206513⟩, ⟨(-71646147874996924), (-70905186813259058)⟩, true⟩

def words04 : List Nat := [360581810970030445, 360581810970806471, 360581810891326760, 360581810589194639, 360581810286943056, 360581809903986316, 360581809806941778, 360581809884459603, 360581809885150805, 360581809825103479]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk557A
