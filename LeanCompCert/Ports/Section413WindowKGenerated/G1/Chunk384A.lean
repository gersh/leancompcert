import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk384A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362497778049808421, 362497798904698406⟩, ⟨(-488734332567126690), (-488193152069692546)⟩, true⟩
def state01 : KState := ⟨⟨362495959631780516, 362495980497859752⟩, ⟨(-418852506037275194), (-418310895814140250)⟩, true⟩
def words00 : List Nat := [371285086547408040, 371285086836904947, 371285087029975013, 371285087223435964, 371285087621819609, 371285087718888863, 371285088461666300, 371285089204926141, 371285089819760122, 371285090104591831]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 38400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 38400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362536839804991644, 362536860682417503⟩, ⟨(-1989263601367810183), (-1988721555264576197)⟩, true⟩
def words01 : List Nat := [371285090966736371, 371285091829495403, 371285093287774300, 371285093843919366, 371285094363322006, 371285094883124228, 371285095907142679, 371285096668728763, 371285098016900871, 371285099365552649]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 38410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 38400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362492213959879302, 362492234848658735⟩, ⟨(-274647565948313925), (-274105083582779069)⟩, true⟩
def words02 : List Nat := [371285100700217082, 371285101133093665, 371285101648632650, 371285102164784702, 371285102784318692, 371285102785575102, 371285102503274525, 371285102220283107, 371285102266298691, 371285102453363719]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 38420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 38400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362467609855273214, 362467630755364086⟩, ⟨671186262924902288, 671729180048301440⟩, true⟩
def words03 : List Nat := [371285103316573519, 371285104180266293, 371285104975471420, 371285105167571438, 371285105565118606, 371285105963251305, 371285106408151916, 371285106409408645, 371285105953088565, 371285105499902284]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 38430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 38400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362491454788905207, 362491475700248296⟩, ⟨(-245502742494688781), (-244959392779166217)⟩, true⟩
def words04 : List Nat := [371285105046173165, 371285105043901159, 371285104955819422, 371285105176153621, 371285105180861595, 371285105182119095, 371285104421319948, 371285104337399736, 371285104843476793, 371285105010467038]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 38440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 38400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk384A
