LOG_FILE="$PWD/storm-log"

touch "$LOG_FILE"
docker run -it \
  -v "$LOG_FILE":/logfile \
  --cap-add=SYS_PTRACE --security-opt seccomp=unconfined \
  storm
