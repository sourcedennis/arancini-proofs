FROM alpine:3.20 AS download

RUN apk upgrade --no-cache &&\
    apk add --no-cache git

WORKDIR /root

RUN git clone --depth 1 https://github.com/sourcedennis/agda-dodo &&\
    cd agda-dodo &&\
    rm -rf .git*

RUN git clone --depth 1 https://github.com/sourcedennis/agda-burrow &&\
    cd agda-burrow &&\
    rm -rf .git*

RUN git clone --depth 1 https://github.com/sourcedennis/arancini-proofs &&\
    cd arancini-proofs &&\
    rm -rf .git*


FROM sourcedennis/agda-mini:2.6.4-1.7.3

RUN echo "/home/proof/agda-dodo/dodo.agda-lib" >> "/home/proof/.agda/libraries" &&\
    echo "/home/proof/agda-burrow/burrow.agda-lib" >> "/home/proof/.agda/libraries"

COPY --from=download --chown=proof:proof /root/agda-dodo /home/proof/agda-dodo
COPY --from=download --chown=proof:proof /root/agda-burrow /home/proof/agda-burrow
COPY --from=download --chown=proof:proof /root/arancini-proofs /home/proof/arancini-proofs

WORKDIR /home/proof/arancini-proofs
