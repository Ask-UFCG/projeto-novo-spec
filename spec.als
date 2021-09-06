module spec

abstract sig Base {
  autor: one Usuario,
  likes: Int,
  dislikes: Int,
  conteudo: one Conteudo
}

sig Questao extends Base {
	respostas: set Resposta,
  titulo: one Titulo
}

sig Titulo{}

sig Conteudo{}

sig Resposta extends Base {
  comentarios: set Comentario
}

sig Usuario{}

sig Comentario extends Base {}

pred likesNaoNegativos[b:Base] {
  b.likes >= 0
}

pred dislikesNaoNegativos[b:Base] {
  b.dislikes >= 0
}

pred umTituloPorQuestao[t:Titulo] {
  one t.~titulo
}

pred umConteudoPorEntidade[c:Conteudo] {
  one c.~conteudo
}

pred questoesSemRespostasIguais[q1:Questao,q2:Questao] {
  (q1 != q2) implies (#(q1.respostas & q2.respostas) = 0)
}

pred respostasSemComentariosIguais[r1:Resposta,r2:Resposta] {
  (r1 != r2) implies (#(r1.comentarios & r2.comentarios) = 0)
}

pred comentarioSempreEmUmaResposta[c:Comentario,r:Resposta] {
  c in r.comentarios
}

pred respsoraSempreEmUmaQuestao[r:Resposta,q:Questao] {
  r in q.respostas
}

fact {
  all b:Base | dislikesNaoNegativos[b]
  all b:Base | likesNaoNegativos[b]
  all t:Titulo | umTituloPorQuestao[t]
  all c:Conteudo | umConteudoPorEntidade[c]
  all q1:Questao | all q2:Questao | questoesSemRespostasIguais[q1,q2]
  all r1:Resposta | all r2:Resposta | respostasSemComentariosIguais[r1,r2]
  all c:Comentario | one r:Resposta | comentarioSempreEmUmaResposta[c,r]
  all r:Resposta | one q:Questao | respsoraSempreEmUmaQuestao[r,q]
}

pred show[]{}
run show for 5