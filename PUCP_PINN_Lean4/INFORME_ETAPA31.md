# Etapa 31 · Interpolación tensorial de Hermite

Base en la [PR #32](https://github.com/MichaelMobius/tesispucp/pull/32), commit `4165c9c4cc2b43fdf53ba6910cf5f119f0e11f47`. Se cotejaron la página impresa 111 y las páginas 116–122 del PDF normativo.

## Problema manufacturado e interpolación

En (3.84)–(3.85), $u^*(x,y)=\sin(\pi x)\sin(\pi y)$, $f=-2\pi^2u^*$ y $a(t)=\sin(\pi t)/(1-t^2)$, con $a(1)=\pi/2$ y $a(-1)=-\pi/2$. `aManufacturadaCompleja_entera` construye la prolongación con esos valores. En cada raíz simple se divide el numerador por el factor lineal mediante su orden analítico. La derivada del numerador identifica el valor del cociente en el punto. `aManufacturada_extension` y `aManufacturada_suave` enlazan esa prolongación con la función real. `solucionManufacturada_factorizada` verifica $u^*=\psi a(x)a(y)$, y `laplaciano_solucionManufacturada` verifica el signo de la fuente.

`existe_unico_hermite` prueba existencia y unicidad para datos arbitrarios de órdenes 0 a 3. Un polinomio con jets nulos es divisible por $\prod_j(X-t_j)^4$. Mathlib aporta la multiplicidad a partir de las derivadas formales, la coprimalidad de los factores en nodos distintos y el grado del producto mónico. La aplicación lineal de los jets tiene dominio y codominio de dimensión $4n$, por lo que la inyectividad implica la sobreyectividad.

`nodosDistintosHermite` toma la imagen finita de cada proyección y `nodosOrdenadosHermite` la enumera en orden creciente. Su cardinal es a lo sumo $m$. Se verifica el caso de una única observación y el de una proyección constante con $m\ge1$. `hermiteMuestra_jet` recupera los datos en cada índice original, incluidos los repetidos.

## Realización y pérdida

`coeficientesHermite325` es el producto tensorial de los coeficientes de ambos interpolantes univariados. `polinomioHermite325_tensor` identifica el producto de sus evaluaciones con el polinomio rectangular y `polinomioHermite325_grado_parcial` certifica ambos grados a lo sumo $4m-1$. `hermite325_jet_mixto` verifica las derivadas iteradas en ambas variables en la cuadrícula de proyecciones.

`proposicion325_interpolacion_exacta` fija la red `red324` antes de cuantificar sobre las muestras. El vector de salida realiza exactamente $h_m=\psi q_xq_y$ y satisface Dirichlet homogéneo. Las reglas de Leibniz y la separación de variables identifican el laplaciano en cada punto original con $f$. La parte empírica de la pérdida es cero como consecuencia de esa igualdad. Estas identidades son válidas incluso en los extremos gracias a la prolongación suave de $a$.

## Contorno y selección

Para $|\zeta|=4$ y $t_j\in[-1,1]$, `productoNodosHermite_contorno` prueba $|\zeta-t_j|\ge3$ en cada factor y $|Q(\zeta)|\ge3^{4n}$ para $Q=\prod_j(z-t_j)^4$. `productoNodosHermite_cociente` verifica $|Q(z)/Q(\zeta)|\le((R+1)/3)^{4n}$ si $|z|\le R$. Así se obtienen $2/3$ en el intervalo y $5/6$ en el disco de radio $3/2$, uniformemente en la separación. `restoContornoHermite_cota` acota el término integral normalizado por $4M((R+1)/3)^{4n}/(4-R)$ si $M$ domina al numerador en el contorno.

`restoContornoHermite_diferencia` aplica Cauchy con orientación positiva y normalización $1/(2\pi i)$ al cociente regularizado de la diferencia con jets nulos. Su numerador es $a-p$. `factorHermite325_jet_complejo` transporta los jets por la restricción al eje real, y `factorHermite325_resto_diferencia` aplica la fórmula a cada interpolante de la muestra. Para la fórmula literal (3.89) todavía se debe demostrar que la contribución de $p$ se anula por $\deg p<4n$. Una ruta para la cancelación usa invariancia de la integral en anillos y la cota $O(|\zeta|^{-2})$ para $p(\zeta)/(Q(\zeta)(\zeta-z))$ en círculos grandes. `derivadas_nucleo_contorno_hermite` verifica la derivación iterada del núcleo de Cauchy. Quedan la cota (3.90) para el error del interpolante real, su transferencia $C^3$ al tensor con $\psi$ y el control Hölder uniforme del laplaciano.

`estratoHermite_measurable` verifica la mensurabilidad de los estratos finitos por orden y `estratoHermite_determina_colisiones` verifica que cada patrón determina las coincidencias. Para completar el selector faltan los representantes de índice fijo por estrato, la continuidad de los coeficientes mediante la inversa de la matriz confluente y el pegado boreliano. `interpolanteHermite` define una función determinada por la unicidad de la inversa lineal.

**Estado de P3.25.** Está verificada la parte algebraica y la interpolación exacta de (3.88). La cota uniforme, la selección boreliana de coeficientes y la realización específica por Horner de ancho ocho siguen pendientes. La realización aquí usa la arquitectura común de L3.24. C3.26 todavía requiere la construcción de minimizadores y su selección boreliana en la clase finita dimensional.

## Verificación

Lean `4.35.0`, Mathlib `v4.35.0` y EllipticPDE `c47acceaf985f59e1cf3257ffea077a73ea99dae`. `lake build` completó 3908 trabajos en el entorno local. Las declaraciones incluyen controles `#check` y `#print axioms`. Las dependencias axiomáticas auditadas son `propext`, `Classical.choice` y `Quot.sound`. El SHA-256 del PDF coincide con el inventario.
