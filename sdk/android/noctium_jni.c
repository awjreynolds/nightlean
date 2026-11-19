#include <jni.h>
#include <stdbool.h>
#include "noctium_control.h"

static void fail(JNIEnv *env, int32_t status) {
    if ((*env)->ExceptionCheck(env)) return;
    jclass type = (*env)->FindClass(env, "org/noctium/sdk/NoctiumFailure");
    if (!type) return;
    jmethodID init = (*env)->GetMethodID(env, type, "<init>", "(I)V");
    if (!init) return;
    jobject error = (*env)->NewObject(env, type, init, (jint)status);
    if (error) (*env)->Throw(env, error);
}

static jbyte *borrow_input(JNIEnv *env, jbyteArray input, jsize *length) {
    *length = input ? (*env)->GetArrayLength(env, input) : 0;
    if (*length <= 0 || *length > 1024 * 1024) {
        fail(env, *length <= 0 ? NOCTIUM_CONTROL_INVALID_ARGUMENT : NOCTIUM_CONTROL_LIMIT);
        return NULL;
    }
    jbyte *bytes = (*env)->GetByteArrayElements(env, input, NULL);
    if (!bytes) fail(env, NOCTIUM_CONTROL_INTERNAL);
    return bytes;
}

static jbyteArray take_result(JNIEnv *env, uint64_t token, bool is_private) {
    int32_t (*length)(uint64_t, size_t *) =
        is_private ? noctium_control_private_length : noctium_control_result_length;
    int32_t (*copy)(uint64_t, uint8_t *, size_t, size_t *) =
        is_private ? noctium_control_private_copy : noctium_control_result_copy;
    int32_t (*free_token)(uint64_t) =
        is_private ? noctium_control_private_free : noctium_control_result_free;
    jbyteArray result = NULL;
    size_t size = 0;
    int32_t status = length(token, &size);
    if (status == NOCTIUM_CONTROL_OK) {
        if (size == 0 || size > INT32_MAX) {
            status = NOCTIUM_CONTROL_INTERNAL;
        } else {
            result = (*env)->NewByteArray(env, (jsize)size);
            jbyte *data = result ? (*env)->GetByteArrayElements(env, result, NULL) : NULL;
            if (data) {
                size_t written = 0;
                status = copy(token, (uint8_t *)data, size, &written);
                if (status == NOCTIUM_CONTROL_OK && written != size)
                    status = NOCTIUM_CONTROL_INTERNAL;
                (*env)->ReleaseByteArrayElements(env, result, data,
                    status == NOCTIUM_CONTROL_OK ? 0 : JNI_ABORT);
            } else {
                status = NOCTIUM_CONTROL_INTERNAL;
            }
        }
    }
    free_token(token);
    if (status != NOCTIUM_CONTROL_OK) {
        fail(env, status);
        return NULL;
    }
    return result;
}

static jbyteArray step(JNIEnv *env, jlong handle,
        int32_t (*operation)(uint64_t, uint64_t *), bool is_private) {
    uint64_t token = 0;
    int32_t status = operation((uint64_t)handle, &token);
    if (status != NOCTIUM_CONTROL_OK) {
        fail(env, status);
        return NULL;
    }
    return take_result(env, token, is_private);
}

JNIEXPORT jlong JNICALL Java_org_noctium_sdk_Native_open(
        JNIEnv *env, jobject self, jbyteArray input) {
    (void)self;
    jsize length;
    jbyte *bytes = borrow_input(env, input, &length);
    if (!bytes) return 0;
    uint64_t handle = 0;
    int32_t status = noctium_control_begin((const uint8_t *)bytes, (size_t)length, &handle);
    (*env)->ReleaseByteArrayElements(env, input, bytes, JNI_ABORT);
    if (status != NOCTIUM_CONTROL_OK) fail(env, status);
    return (jlong)handle;
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_Native_advance(
        JNIEnv *env, jobject self, jlong handle) {
    (void)self;
    return step(env, handle, noctium_control_advance, false);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_Native_resume(
        JNIEnv *env, jobject self, jlong handle, jbyteArray response, jboolean typed) {
    (void)self;
    jsize length;
    jbyte *bytes = borrow_input(env, response, &length);
    if (!bytes) return NULL;
    uint64_t token = 0;
    int32_t (*resume)(uint64_t, const uint8_t *, size_t, uint64_t *) =
        typed ? noctium_control_resume_typed : noctium_control_resume;
    int32_t status = resume((uint64_t)handle, (const uint8_t *)bytes, (size_t)length, &token);
    (*env)->ReleaseByteArrayElements(env, response, bytes, JNI_ABORT);
    if (status != NOCTIUM_CONTROL_OK) {
        fail(env, status);
        return NULL;
    }
    return take_result(env, token, false);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_Native_privateRequest(
        JNIEnv *env, jobject self, jlong handle) {
    (void)self;
    return step(env, handle, noctium_control_private_request, true);
}

JNIEXPORT jbyteArray JNICALL Java_org_noctium_sdk_Native_cancel(
        JNIEnv *env, jobject self, jlong handle) {
    (void)self;
    return step(env, handle, noctium_control_cancel, false);
}

JNIEXPORT void JNICALL Java_org_noctium_sdk_Native_close(
        JNIEnv *env, jobject self, jlong handle) {
    (void)self;
    int32_t status = noctium_control_free((uint64_t)handle);
    if (status != NOCTIUM_CONTROL_OK) fail(env, status);
}
