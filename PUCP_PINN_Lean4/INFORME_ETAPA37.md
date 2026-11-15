# Etapa 37 · generalización dimensional de T3.4, T3.8 y P3.14

Base [PR #38](https://github.com/MichaelMobius/tesispucp/pull/38), commit `4581fd0b2d07b6b6dd36723c3178a69b58660ebb`. El cotejo usa el PDF normativo, pp. impresas 48–50, 64–73 y 83–85, y los Teoremas 3.1 y 3.2 y los apéndices B–C del artículo. [Shin, Darbon y Karniadakis](https://arxiv.org/pdf/2004.01806)

## Teorema 3.4

`DatosMasaDimensional` separa las propiedades deterministas del soporte y de la ley de las propiedades probabilísticas de las muestras, expresadas en `Muestreo38`. Sobre espacios pseudométricos con abiertos medibles, el registro contiene concentración, acotación, cota superior para bolas cerradas, y particiones de diámetro $D\eta$ y masa mínima $c\eta^s$. `teorema34_dimensional` toma $D=\sqrt d$, $s_r=d$ y $s_b=d-1$ para $d\ge2$. Las pruebas de la etapa usan residuos reales. Las cotas Hölder se formulan con $\alpha>0$, que incluye el intervalo $0<\alpha\le1$ del texto. La realización geométrica de los datos se debe justificar para cada dominio.

Para un tamaño positivo, la escala auxiliar es $(1/(c\sqrt m))^{1/s}$. El radio final $D$ veces esa escala debe ser a lo sumo $\varepsilon_0$. Como $D\ge1$, esto también autoriza el uso de la partición. La fórmula de masa auxiliar da exactamente $1/\sqrt m$. El recuento de L3.6 da a lo sumo $\sqrt m$ celdas y la ocupación binomial controla el fallo por $\sqrt m(1-1/\sqrt m)^m$. `evento_cobertura34_dimensional` intersecta los dos eventos medibles de ocupación con los dos de pertenencia a los soportes. Esos últimos tienen complemento nulo por concentración. La cota de unión da exactamente (3.10), con dos términos de fallo. La independencia interna de cada familia se usa para calcular la probabilidad de celda vacía. Para la intersección de eventos se usa la cota de unión, que es la convención de la tesis.

`cota34_dimensional_bajo_cobertura` absorbe las sumas de los residuos de L3.5. Para radios $r,b$, el factor es $3\max(C_r m_r r^{s_r},C_b m_b b^{s_b})$. La cancelación de los tamaños reproduce los promedios $\lambda_r/m_r$ y $\lambda_b/m_b$. En la escala raíz, `factorCoberturaDimensional_raiz` identifica este factor con (3.6). Los pesos separados son $3\lambda_r r^{2\alpha}/C_m$ y $3\lambda_b b^{2\alpha}/C_m$. También se verifica la cota con ambos pesos iguales al máximo, opción que usa T3.8. `constante34Dimensional_eq` identifica $C'$ con (3.9), y el resto de datos se acota por $C'(m_r^{-\alpha/d}+m_b^{-\alpha/(d-1)})$. La integrabilidad se deduce de Hölder, concentración y acotación.

El orden de cuantificadores de `teorema34_dimensional` es $\exists A$ medible con (3.10), $\forall\omega\in A$, $\forall h\in\mathcal H_m$. La elección de $A$ utiliza los prefijos y las celdas, por lo que un candidato puede depender de la muestra. El artículo formula una cota mediante un producto de probabilidades bajo su estructura de muestreo. El resultado Lean sigue la intersección y la normalización de masa mínima de (3.10) del PDF normativo.

## Teorema 3.8

`teorema38_evento_dimensional` da la forma de muestra finita de (3.26) en el evento de cobertura. Para cada realización se pueden elegir el minimizador, un comparador exacto y la cota $R$ de su regularidad dentro del evento. El funcional es el de (3.23) con pesos iguales $a_m>0$. Minimalidad e interpolación empírica exacta dan (3.29) y (3.30). El producto $C_ma_m$ es el máximo de $3\lambda_r r^{2\alpha}$ y $3\lambda_b b^{2\alpha}$. Ese máximo y las contribuciones de los datos dan una cota explícita de pérdida.

`tasa_frontera_dimensional_le` eleva $m_r\le K m_b^{s_r/s_b}$ a $\alpha/s_r>0$ y toma recíprocos. Obtiene $m_b^{-\alpha/s_b}\le K^{\alpha/s_r}m_r^{-\alpha/s_r}$. La especialización $s_r=d,s_b=d-1$ recupera la comparabilidad del texto. Para $d=2$ coincide con $m_r\le K m_b^2$.

`teorema38_dimension_ge_dos` obtiene (3.26)–(3.28) en el mismo evento casi seguro. A lo largo de los tamaños $m_r(n),m_b(n)\ge n$ eventualmente, los radios entran en el intervalo admisible. La ocupación eventual usa la cota sumable de los fallos y Borel–Cantelli. Se intersectan las dos coberturas, los eventos de pertenencia y las premisas variacionales. Los registros conservan las selecciones mensurables, la interpolación exacta y una cota $R$ uniforme en el índice, que puede depender de la realización. La existencia de comparadores y minimizadores para una arquitectura general queda a cargo de la aplicación.

La energía de cada residuo es de orden $m_r^{-\alpha/d}$ porque su peso residual es fijo y positivo. La regularidad controlada por (3.29) da constantes Hölder uniformes $\sqrt R+S_f$ y $\sqrt R+S_g$. La masa local de L3.3 y `lema39_tasa` dan convergencia de ambos supremos y los exponentes impresos

\[
\frac{\alpha^2}{d(2\alpha+d)},\qquad
\frac{\alpha^2}{d(2\alpha+d-1)}.
\]

El factor $2$ del encargo en esos denominadores corresponde a $d=2$. Lean usa el supremo de los residuos en los soportes. En los espacios del enunciado, si las funciones se consideran continuas en la clausura, el supremo sobre el interior denso da el mismo control. Las conclusiones se expresan mediante `∀ᵐ`, que proporciona una propiedad en un conjunto de medida plena. La mensurabilidad por separado del conjunto exacto de convergencia o de la pérdida escalar puede requerir las hipótesis adicionales de mensurabilidad conjunta y separabilidad indicadas en `Teorema38.lean`.

## Especializaciones en dimensión dos

`problemaRaizDimensional_dim2` y `problemaRaizDimensional_igual_dim2` identifican los problemas, incluidos pesos y prefijos. `teorema34_dim2_de_dimensional` y `teorema38_dim2_de_dimensional` recuperan los enunciados anteriores directamente. Las demostraciones originales siguen en sus módulos.

`teorema34_cuadrado_dos_familias` aplica T3.4 al espacio producto de `probabilidadMuestrasCuadrado`. La ley interior tiene densidad $1/4$ respecto de área y la ley de frontera es $\mathcal H^1/8$. Los parámetros son $c_r=1/9, C_r=\pi/4, c_b=1/12,C_b=1,\varepsilon_0=1$. Los umbrales $m_r\ge324$ y $m_b\ge288$ aseguran que los radios $3\sqrt2\,m_r^{-1/4}$ y $12\sqrt2/\sqrt{m_b}$ están dentro del intervalo. Se usa exactamente la misma cota de probabilidad de dos fallos. El modelo producto sí demuestra independencia de las dos sucesiones completas. Ello satisface la parte muestral, mientras que H3.7 describe clases y comparadores.

## Proposición 3.14

`proposicion314_evento_dimensional` aplica L3.13 a ambas leyes. En los tamaños admisibles, el evento común tiene la cota (3.61). Su desigualdad simultánea de pérdidas usa los radios (3.59), el factor y el peso igual de (3.60), y conserva los dos términos de datos de (3.62). `proposicion314_dimensional` aplica Borel–Cantelli mediante L3.13 y exige las premisas variacionales del funcional con esos pesos. La tasa resultante es

\[
O\left((\log m_r/m_r)^{2\alpha/s_r}
       +(\log m_b/m_b)^{2\alpha/s_b}\right),
\]

con $s_r=d,s_b=d-1$ en (3.63). Cada peso y el factor coinciden con las fórmulas normativas en los tamaños admisibles. El constructor usa un radio auxiliar positivo para tamaños menores que tres, fuera de las afirmaciones del evento y de la cola logarítmica. La tasa admite comparadores y mínimos verificados eventualmente. No se usa una relación de comparabilidad entre tamaños en P3.14.

## Caso unidimensional y obligaciones restantes

La ecuación (3.12) usa una sola cobertura y datos disponibles en los dos extremos, con pérdida de frontera determinista $\tfrac{\lambda_b}{2}(|B[h](a)-g(a)|^2+|B[h](b)-g(b)|^2)$. El factor correcto es $\max(1,3 C_r m_r\varepsilon_r)$, con $\varepsilon_r=c_r^{-1}m_r^{-1/2}$ y regularización interior únicamente. Quedan el funcional de los dos extremos y su integración con la cobertura interior y la tasa $O(m_r^{-\alpha})$. Los exponentes positivos de masa del caso general no se instancian con $s_b=0$.

El [inventario](INVENTARIO_FORMAL_CAPITULO_III.md) distingue la generalidad de masa de la realización en dominios euclidianos. También quedan P3.10 en dimensión arbitraria, la existencia clásica de T3.18, la extensión de T3.20 a dominios Lipschitz generales y la formulación multiíndice literal de L3.1.

## Verificación

`lake build` completó 4027 trabajos con Lean 4.35.0, Mathlib v4.35.0 y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. Las declaraciones principales se verificaron con `#check` y `#print axioms` y dependen de `propext`, `Classical.choice` y `Quot.sound`. El PDF conserva SHA-256 `c6c612f7141c8c6ab5730fc0853b6d16222b97e5615e306f2e32191a49b686e0`.
