FROM ubuntu

# insert pre-built test binary & tests
COPY test .
COPY src/ src/

# also insert sqlite database
COPY chinook.db .

ENTRYPOINT test
